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
                                   FStar_TypeChecker_Env.inst_tscheme
                                     (annotated_univ_names,
                                       (ed2.FStar_Syntax_Syntax.signature))
                                    in
                                 (match uu____1527 with
                                  | (uu____1540,signature1) ->
                                      let new_univs =
                                        FStar_All.pipe_right
                                          annotated_univ_names
                                          (FStar_List.map
                                             (fun uu____1546  ->
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()))
                                         in
                                      let u_subst =
                                        FStar_TypeChecker_Env.mk_univ_subst
                                          annotated_univ_names new_univs
                                         in
                                      let uu____1550 =
                                        get_binders_from_signature signature1
                                         in
                                      let uu____1551 =
                                        FStar_Syntax_Subst.subst u_subst repr
                                         in
                                      (uu____1550, uu____1551))
                              in
                           (match uu____1494 with
                            | (b_bs,b_repr) ->
                                let b_bs1 =
                                  FStar_Syntax_Subst.open_binders b_bs  in
                                let uu____1559 =
                                  let uu____1578 = FStar_List.hd b_bs1  in
                                  let uu____1591 = FStar_List.tl b_bs1  in
                                  (uu____1578, uu____1591)  in
                                (match uu____1559 with
                                 | (b,b_bs_indices) ->
                                     let b_bs_indices_arrow =
                                       FStar_All.pipe_right b_bs_indices
                                         (FStar_List.map
                                            (fun uu____1695  ->
                                               match uu____1695 with
                                               | (b1,q) ->
                                                   let uu____1714 =
                                                     let uu___216_1715 = b1
                                                        in
                                                     let uu____1716 =
                                                       let uu____1719 =
                                                         let uu____1728 =
                                                           let uu____1735 =
                                                             let uu____1736 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____1736
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____1735
                                                            in
                                                         [uu____1728]  in
                                                       let uu____1757 =
                                                         FStar_Syntax_Syntax.mk_Total
                                                           b1.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         uu____1719
                                                         uu____1757
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.ppname
                                                         =
                                                         (uu___216_1715.FStar_Syntax_Syntax.ppname);
                                                       FStar_Syntax_Syntax.index
                                                         =
                                                         (uu___216_1715.FStar_Syntax_Syntax.index);
                                                       FStar_Syntax_Syntax.sort
                                                         = uu____1716
                                                     }  in
                                                   (uu____1714, q)))
                                        in
                                     let f_b =
                                       let uu____1763 =
                                         let uu____1764 =
                                           let uu____1769 =
                                             let uu____1770 =
                                               let uu____1773 =
                                                 FStar_All.pipe_right (a ::
                                                   bs_indices)
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____1773
                                                 (FStar_List.map
                                                    FStar_Syntax_Syntax.bv_to_name)
                                                in
                                             FStar_All.pipe_right uu____1770
                                               (FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____1769
                                            in
                                         uu____1764
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                          in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____1763
                                        in
                                     let g_b =
                                       let b_arg =
                                         let uu____1816 =
                                           let uu____1817 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____1817
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_All.pipe_right uu____1816
                                           FStar_Syntax_Syntax.as_arg
                                          in
                                       let x =
                                         let uu____1835 =
                                           let uu____1836 =
                                             FStar_All.pipe_right a
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____1836
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_Syntax_Syntax.null_binder
                                           uu____1835
                                          in
                                       let b_indices_args =
                                         let uu____1856 =
                                           let uu____1859 =
                                             FStar_All.pipe_right
                                               b_bs_indices_arrow
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst)
                                              in
                                           FStar_All.pipe_right uu____1859
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.bv_to_name)
                                            in
                                         FStar_All.pipe_right uu____1856
                                           (FStar_List.map
                                              (fun t  ->
                                                 let uu____1899 =
                                                   let uu____1900 =
                                                     let uu____1905 =
                                                       let uu____1906 =
                                                         let uu____1915 =
                                                           let uu____1916 =
                                                             FStar_All.pipe_right
                                                               x
                                                               FStar_Pervasives_Native.fst
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____1916
                                                             FStar_Syntax_Syntax.bv_to_name
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____1915
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____1906]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       t uu____1905
                                                      in
                                                   uu____1900
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1899
                                                   FStar_Syntax_Syntax.as_arg))
                                          in
                                       let repr_app =
                                         FStar_Syntax_Syntax.mk_Tm_app b_repr
                                           (b_arg :: b_indices_args)
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                          in
                                       let uu____1960 =
                                         let uu____1961 =
                                           FStar_Syntax_Syntax.mk_Total
                                             repr_app
                                            in
                                         FStar_Syntax_Util.arrow [x]
                                           uu____1961
                                          in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____1960
                                        in
                                     let bs2 = a :: b ::
                                       (FStar_List.append bs_indices
                                          (FStar_List.append
                                             b_bs_indices_arrow [f_b; g_b]))
                                        in
                                     let uu____2027 =
                                       let env1 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs2
                                          in
                                       FStar_List.fold_left
                                         (fun uu____2071  ->
                                            fun uu____2072  ->
                                              match (uu____2071, uu____2072)
                                              with
                                              | ((uvars1,gs,bs_substs),
                                                 (b1,uu____2125)) ->
                                                  let uu____2160 =
                                                    let uu____2173 =
                                                      FStar_Syntax_Subst.subst
                                                        bs_substs
                                                        b1.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      "" r env1 uu____2173
                                                     in
                                                  (match uu____2160 with
                                                   | (t,uu____2188,g) ->
                                                       let uu____2202 =
                                                         let uu____2205 =
                                                           let uu____2208 =
                                                             FStar_All.pipe_right
                                                               t
                                                               FStar_Syntax_Syntax.as_arg
                                                              in
                                                           [uu____2208]  in
                                                         FStar_List.append
                                                           uvars1 uu____2205
                                                          in
                                                       (uu____2202,
                                                         (FStar_List.append
                                                            gs [g]),
                                                         (FStar_List.append
                                                            bs_substs
                                                            [FStar_Syntax_Syntax.NT
                                                               (b1, t)]))))
                                         ([], [], []) b_bs_indices
                                        in
                                     (match uu____2027 with
                                      | (uvars1,gs,uu____2229) ->
                                          let expected_bind_repr_type =
                                            let repr_args =
                                              let uu____2248 =
                                                FStar_Syntax_Util.arg_of_non_null_binder
                                                  b
                                                 in
                                              uu____2248 :: uvars1  in
                                            let repr_comp =
                                              let uu____2252 =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  b_repr repr_args
                                                  FStar_Pervasives_Native.None
                                                  r
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____2252
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
                                          ((let uu____2256 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffects")
                                               in
                                            if uu____2256
                                            then
                                              let uu____2261 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  ed2.FStar_Syntax_Syntax.bind_repr
                                                 in
                                              let uu____2263 =
                                                FStar_Syntax_Print.term_to_string
                                                  expected_bind_repr_type
                                                 in
                                              FStar_Util.print2
                                                "Checking bind_repr: %s against expected bind_repr type: %s\n"
                                                uu____2261 uu____2263
                                            else ());
                                           (let bind_repr =
                                              check_and_gen1
                                                (let uu___250_2279 = env  in
                                                 {
                                                   FStar_TypeChecker_Env.solver
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.solver);
                                                   FStar_TypeChecker_Env.range
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.range);
                                                   FStar_TypeChecker_Env.curmodule
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.curmodule);
                                                   FStar_TypeChecker_Env.gamma
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.gamma);
                                                   FStar_TypeChecker_Env.gamma_sig
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.gamma_sig);
                                                   FStar_TypeChecker_Env.gamma_cache
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.gamma_cache);
                                                   FStar_TypeChecker_Env.modules
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.modules);
                                                   FStar_TypeChecker_Env.expected_typ
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.expected_typ);
                                                   FStar_TypeChecker_Env.sigtab
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.sigtab);
                                                   FStar_TypeChecker_Env.attrtab
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.attrtab);
                                                   FStar_TypeChecker_Env.is_pattern
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.is_pattern);
                                                   FStar_TypeChecker_Env.instantiate_imp
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.instantiate_imp);
                                                   FStar_TypeChecker_Env.effects
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.effects);
                                                   FStar_TypeChecker_Env.generalize
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.generalize);
                                                   FStar_TypeChecker_Env.letrecs
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.letrecs);
                                                   FStar_TypeChecker_Env.top_level
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.top_level);
                                                   FStar_TypeChecker_Env.check_uvars
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.check_uvars);
                                                   FStar_TypeChecker_Env.use_eq
                                                     = true;
                                                   FStar_TypeChecker_Env.is_iface
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.is_iface);
                                                   FStar_TypeChecker_Env.admit
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.admit);
                                                   FStar_TypeChecker_Env.lax
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.lax);
                                                   FStar_TypeChecker_Env.lax_universes
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.lax_universes);
                                                   FStar_TypeChecker_Env.phase1
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.phase1);
                                                   FStar_TypeChecker_Env.failhard
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.failhard);
                                                   FStar_TypeChecker_Env.nosynth
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.nosynth);
                                                   FStar_TypeChecker_Env.uvar_subtyping
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.uvar_subtyping);
                                                   FStar_TypeChecker_Env.tc_term
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.tc_term);
                                                   FStar_TypeChecker_Env.type_of
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.type_of);
                                                   FStar_TypeChecker_Env.universe_of
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.universe_of);
                                                   FStar_TypeChecker_Env.check_type_of
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.check_type_of);
                                                   FStar_TypeChecker_Env.use_bv_sorts
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.use_bv_sorts);
                                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                   FStar_TypeChecker_Env.normalized_eff_names
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.normalized_eff_names);
                                                   FStar_TypeChecker_Env.fv_delta_depths
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.fv_delta_depths);
                                                   FStar_TypeChecker_Env.proof_ns
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.proof_ns);
                                                   FStar_TypeChecker_Env.synth_hook
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.synth_hook);
                                                   FStar_TypeChecker_Env.splice
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.splice);
                                                   FStar_TypeChecker_Env.postprocess
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.postprocess);
                                                   FStar_TypeChecker_Env.is_native_tactic
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.is_native_tactic);
                                                   FStar_TypeChecker_Env.identifier_info
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.identifier_info);
                                                   FStar_TypeChecker_Env.tc_hooks
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.tc_hooks);
                                                   FStar_TypeChecker_Env.dsenv
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.dsenv);
                                                   FStar_TypeChecker_Env.nbe
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.nbe);
                                                   FStar_TypeChecker_Env.strict_args_tab
                                                     =
                                                     (uu___250_2279.FStar_TypeChecker_Env.strict_args_tab)
                                                 })
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_bind_repr_type
                                               in
                                            FStar_List.iter
                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                 env) gs;
                                            (let uu____2283 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2283
                                             then
                                               let uu____2288 =
                                                 FStar_Syntax_Print.tscheme_to_string
                                                   bind_repr
                                                  in
                                               let uu____2290 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_bind_repr_type
                                                  in
                                               FStar_Util.print2
                                                 "Checked bind_repr: %s against expected bind_repr type: %s\n"
                                                 uu____2288 uu____2290
                                             else ());
                                            (let bs3 = a :: b ::
                                               (FStar_List.append bs_indices
                                                  b_bs_indices_arrow)
                                                in
                                             let indices =
                                               let uu____2325 =
                                                 FStar_All.pipe_right uvars1
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2325
                                                 (FStar_List.map
                                                    FStar_Syntax_Subst.compress)
                                                in
                                             let embedded_indices =
                                               let uu____2351 =
                                                 let uu____2358 =
                                                   FStar_Syntax_Embeddings.e_list
                                                     FStar_Syntax_Embeddings.e_any
                                                    in
                                                 FStar_Syntax_Embeddings.embed
                                                   uu____2358 indices
                                                  in
                                               uu____2351
                                                 FStar_Range.dummyRange
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Embeddings.id_norm_cb
                                                in
                                             let bind_wp =
                                               let uu____2368 =
                                                 let uu____2369 =
                                                   FStar_Syntax_Subst.close_binders
                                                     bs3
                                                    in
                                                 let uu____2370 =
                                                   FStar_Syntax_Subst.close
                                                     bs3 embedded_indices
                                                    in
                                                 FStar_Syntax_Util.abs
                                                   uu____2369 uu____2370
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2368
                                                 (FStar_TypeChecker_Util.generalize_universes
                                                    env)
                                                in
                                             (let uu____2374 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____2374
                                              then
                                                let uu____2379 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    bind_wp
                                                   in
                                                FStar_Util.print1
                                                  "bind_wp: %s\n" uu____2379
                                              else ());
                                             (bind_repr, bind_wp)))))))
                        in
                     (match uu____1392 with
                      | (bind_repr,bind_wp) ->
                          let uu____2386 =
                            let uu____2391 =
                              FStar_TypeChecker_Util.generalize_universes
                                env0 ed2.FStar_Syntax_Syntax.signature
                               in
                            match uu____2391 with
                            | (univs1,signature1) ->
                                (match annotated_univ_names with
                                 | [] -> (univs1, signature1)
                                 | uu____2410 ->
                                     let uu____2413 =
                                       ((FStar_List.length univs1) =
                                          (FStar_List.length
                                             annotated_univ_names))
                                         &&
                                         (FStar_List.forall2
                                            (fun u1  ->
                                               fun u2  ->
                                                 let uu____2420 =
                                                   FStar_Syntax_Syntax.order_univ_name
                                                     u1 u2
                                                    in
                                                 uu____2420 = Prims.int_zero)
                                            univs1 annotated_univ_names)
                                        in
                                     if uu____2413
                                     then (univs1, signature1)
                                     else
                                       (let uu____2431 =
                                          let uu____2437 =
                                            let uu____2439 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length
                                                   annotated_univ_names)
                                               in
                                            let uu____2441 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length univs1)
                                               in
                                            FStar_Util.format2
                                              "Expected an effect definition with %s universes; but found %s"
                                              uu____2439 uu____2441
                                             in
                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                            uu____2437)
                                           in
                                        FStar_Errors.raise_error uu____2431
                                          (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                             in
                          (match uu____2386 with
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
                                 (let uu____2471 =
                                    ((n1 >= Prims.int_zero) &&
                                       (let uu____2475 =
                                          FStar_Syntax_Util.is_unknown
                                            (FStar_Pervasives_Native.snd ts1)
                                           in
                                        Prims.op_Negation uu____2475))
                                      && (m <> n1)
                                     in
                                  if uu____2471
                                  then
                                    let error =
                                      if m < n1
                                      then "not universe-polymorphic enough"
                                      else "too universe-polymorphic"  in
                                    let err_msg =
                                      let uu____2493 =
                                        FStar_Util.string_of_int m  in
                                      let uu____2495 =
                                        FStar_Util.string_of_int n1  in
                                      let uu____2497 =
                                        FStar_Syntax_Print.tscheme_to_string
                                          ts1
                                         in
                                      FStar_Util.format4
                                        "The effect combinator is %s (m,n=%s,%s) (%s)"
                                        error uu____2493 uu____2495
                                        uu____2497
                                       in
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                        err_msg)
                                      (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos
                                  else ());
                                 ts1  in
                               let ed3 =
                                 let uu___286_2508 = ed2  in
                                 let uu____2509 =
                                   close1 Prims.int_zero return_wp  in
                                 let uu____2511 =
                                   close1 Prims.int_one bind_wp  in
                                 let uu____2513 =
                                   close1 Prims.int_zero return_repr  in
                                 let uu____2515 =
                                   close1 Prims.int_one bind_repr  in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___286_2508.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___286_2508.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___286_2508.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs = univs1;
                                   FStar_Syntax_Syntax.binders = [];
                                   FStar_Syntax_Syntax.signature = signature1;
                                   FStar_Syntax_Syntax.ret_wp = uu____2509;
                                   FStar_Syntax_Syntax.bind_wp = uu____2511;
                                   FStar_Syntax_Syntax.stronger =
                                     (uu___286_2508.FStar_Syntax_Syntax.stronger);
                                   FStar_Syntax_Syntax.match_wps =
                                     (uu___286_2508.FStar_Syntax_Syntax.match_wps);
                                   FStar_Syntax_Syntax.trivial =
                                     (uu___286_2508.FStar_Syntax_Syntax.trivial);
                                   FStar_Syntax_Syntax.repr = repr;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____2513;
                                   FStar_Syntax_Syntax.bind_repr = uu____2515;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     (uu___286_2508.FStar_Syntax_Syntax.stronger_repr);
                                   FStar_Syntax_Syntax.actions =
                                     (uu___286_2508.FStar_Syntax_Syntax.actions);
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___286_2508.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____2524 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____2524
                                 then
                                   let uu____2529 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked layered effect: %s\n"
                                     uu____2529
                                 else ());
                                failwith "That's it for now"))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____2547 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____2547 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____2579 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____2579 t  in
          let open_univs_binders n_binders bs =
            let uu____2595 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____2595 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____2605 =
            let uu____2612 =
              open_univs_binders Prims.int_zero
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____2614 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____2612 uu____2614  in
          (match uu____2605 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____2619 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____2619 with
                | (effect_params,env1,uu____2628) ->
                    let uu____2629 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____2629 with
                     | (signature,uu____2635) ->
                         let ed1 =
                           let uu___315_2637 = ed  in
                           {
                             FStar_Syntax_Syntax.is_layered =
                               (uu___315_2637.FStar_Syntax_Syntax.is_layered);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___315_2637.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___315_2637.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___315_2637.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___315_2637.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___315_2637.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___315_2637.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.match_wps =
                               (uu___315_2637.FStar_Syntax_Syntax.match_wps);
                             FStar_Syntax_Syntax.trivial =
                               (uu___315_2637.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___315_2637.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___315_2637.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___315_2637.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.stronger_repr =
                               (uu___315_2637.FStar_Syntax_Syntax.stronger_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___315_2637.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___315_2637.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____2665 ->
                               let op uu____2697 =
                                 match uu____2697 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____2717 =
                                       let uu____2718 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____2721 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____2718
                                         uu____2721
                                        in
                                     (us, uu____2717)
                                  in
                               let uu___327_2724 = ed1  in
                               let uu____2725 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____2726 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____2727 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____2728 =
                                 FStar_Syntax_Util.map_match_wps op
                                   ed1.FStar_Syntax_Syntax.match_wps
                                  in
                               let uu____2733 =
                                 FStar_Util.map_opt
                                   ed1.FStar_Syntax_Syntax.trivial op
                                  in
                               let uu____2736 =
                                 let uu____2737 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____2737  in
                               let uu____2748 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____2749 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____2750 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___330_2758 = a  in
                                      let uu____2759 =
                                        let uu____2760 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd
                                          uu____2760
                                         in
                                      let uu____2771 =
                                        let uu____2772 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd
                                          uu____2772
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___330_2758.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___330_2758.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___330_2758.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___330_2758.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____2759;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____2771
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.is_layered =
                                   (uu___327_2724.FStar_Syntax_Syntax.is_layered);
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___327_2724.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___327_2724.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___327_2724.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___327_2724.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____2725;
                                 FStar_Syntax_Syntax.bind_wp = uu____2726;
                                 FStar_Syntax_Syntax.stronger = uu____2727;
                                 FStar_Syntax_Syntax.match_wps = uu____2728;
                                 FStar_Syntax_Syntax.trivial = uu____2733;
                                 FStar_Syntax_Syntax.repr = uu____2736;
                                 FStar_Syntax_Syntax.return_repr = uu____2748;
                                 FStar_Syntax_Syntax.bind_repr = uu____2749;
                                 FStar_Syntax_Syntax.stronger_repr =
                                   (uu___327_2724.FStar_Syntax_Syntax.stronger_repr);
                                 FStar_Syntax_Syntax.actions = uu____2750;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___327_2724.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____2817 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____2823 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____2817 uu____2823
                              in
                           let uu____2830 =
                             let uu____2831 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____2831.FStar_Syntax_Syntax.n  in
                           match uu____2830 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____2870)::(wp,uu____2872)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____2901 -> fail1 signature1)
                           | uu____2902 -> fail1 signature1  in
                         let uu____2903 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____2903 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____2927 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____2934 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____2934 with
                                     | (signature1,uu____2946) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____2947 ->
                                    let uu____2950 =
                                      let uu____2955 =
                                        let uu____2956 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____2956)
                                         in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____2955
                                       in
                                    (match uu____2950 with
                                     | (uu____2969,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____2972 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____2972
                                 in
                              ((let uu____2974 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____2974
                                then
                                  let uu____2979 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____2981 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____2984 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____2986 =
                                    let uu____2988 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____2988
                                     in
                                  let uu____2989 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____2979 uu____2981 uu____2984
                                    uu____2986 uu____2989
                                else ());
                               (let check_and_gen' env3 uu____3024 k =
                                  match uu____3024 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____3060::uu____3061 ->
                                           let uu____3064 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____3064 with
                                            | (us1,t1) ->
                                                let uu____3087 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____3087 with
                                                 | (us2,t2) ->
                                                     let uu____3102 =
                                                       let uu____3103 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____3103 t2 k
                                                        in
                                                     let uu____3104 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____3104))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____3123 =
                                      let uu____3132 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____3139 =
                                        let uu____3148 =
                                          let uu____3155 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____3155
                                           in
                                        [uu____3148]  in
                                      uu____3132 :: uu____3139  in
                                    let uu____3174 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____3123
                                      uu____3174
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____3178 = fresh_effect_signature ()
                                     in
                                  match uu____3178 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____3194 =
                                          let uu____3203 =
                                            let uu____3210 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____3210
                                             in
                                          [uu____3203]  in
                                        let uu____3223 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____3194
                                          uu____3223
                                         in
                                      let expected_k =
                                        let uu____3229 =
                                          let uu____3238 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____3245 =
                                            let uu____3254 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____3261 =
                                              let uu____3270 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____3277 =
                                                let uu____3286 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____3293 =
                                                  let uu____3302 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____3302]  in
                                                uu____3286 :: uu____3293  in
                                              uu____3270 :: uu____3277  in
                                            uu____3254 :: uu____3261  in
                                          uu____3238 :: uu____3245  in
                                        let uu____3345 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____3229
                                          uu____3345
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let uu____3348 =
                                  FStar_Syntax_Util.get_match_with_close_wps
                                    ed2.FStar_Syntax_Syntax.match_wps
                                   in
                                match uu____3348 with
                                | (if_then_else1,ite_wp,close_wp) ->
                                    let if_then_else2 =
                                      let p =
                                        let uu____3368 =
                                          let uu____3371 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____3371
                                           in
                                        let uu____3372 =
                                          let uu____3373 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____3373
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____3368
                                          uu____3372
                                         in
                                      let expected_k =
                                        let uu____3385 =
                                          let uu____3394 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3401 =
                                            let uu____3410 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____3417 =
                                              let uu____3426 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____3433 =
                                                let uu____3442 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____3442]  in
                                              uu____3426 :: uu____3433  in
                                            uu____3410 :: uu____3417  in
                                          uu____3394 :: uu____3401  in
                                        let uu____3479 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3385
                                          uu____3479
                                         in
                                      check_and_gen' env2 if_then_else1
                                        expected_k
                                       in
                                    let ite_wp1 =
                                      let expected_k =
                                        let uu____3494 =
                                          let uu____3503 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3510 =
                                            let uu____3519 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____3519]  in
                                          uu____3503 :: uu____3510  in
                                        let uu____3544 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3494
                                          uu____3544
                                         in
                                      check_and_gen' env2 ite_wp expected_k
                                       in
                                    let close_wp1 =
                                      let b =
                                        let uu____3557 =
                                          let uu____3560 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____3560
                                           in
                                        let uu____3561 =
                                          let uu____3562 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____3562
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____3557
                                          uu____3561
                                         in
                                      let b_wp_a =
                                        let uu____3574 =
                                          let uu____3583 =
                                            let uu____3590 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____3590
                                             in
                                          [uu____3583]  in
                                        let uu____3603 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3574
                                          uu____3603
                                         in
                                      let expected_k =
                                        let uu____3609 =
                                          let uu____3618 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3625 =
                                            let uu____3634 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____3641 =
                                              let uu____3650 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____3650]  in
                                            uu____3634 :: uu____3641  in
                                          uu____3618 :: uu____3625  in
                                        let uu____3681 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3609
                                          uu____3681
                                         in
                                      check_and_gen' env2 close_wp expected_k
                                       in
                                    let stronger =
                                      let uu____3685 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____3685 with
                                      | (t,uu____3691) ->
                                          let expected_k =
                                            let uu____3695 =
                                              let uu____3704 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____3711 =
                                                let uu____3720 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____3727 =
                                                  let uu____3736 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____3736]  in
                                                uu____3720 :: uu____3727  in
                                              uu____3704 :: uu____3711  in
                                            let uu____3767 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3695 uu____3767
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
                                          let uu____3776 =
                                            FStar_Syntax_Util.type_u ()  in
                                          (match uu____3776 with
                                           | (t,uu____3784) ->
                                               let expected_k =
                                                 let uu____3788 =
                                                   let uu____3797 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       a
                                                      in
                                                   let uu____3804 =
                                                     let uu____3813 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         wp_a
                                                        in
                                                     [uu____3813]  in
                                                   uu____3797 :: uu____3804
                                                    in
                                                 let uu____3838 =
                                                   FStar_Syntax_Syntax.mk_GTotal
                                                     t
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____3788 uu____3838
                                                  in
                                               let uu____3841 =
                                                 check_and_gen' env2 trivial
                                                   expected_k
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____3841)
                                       in
                                    let uu____3842 =
                                      let uu____3855 =
                                        let uu____3856 =
                                          FStar_Syntax_Subst.compress
                                            ed2.FStar_Syntax_Syntax.repr
                                           in
                                        uu____3856.FStar_Syntax_Syntax.n  in
                                      match uu____3855 with
                                      | FStar_Syntax_Syntax.Tm_unknown  ->
                                          ((ed2.FStar_Syntax_Syntax.repr),
                                            (ed2.FStar_Syntax_Syntax.bind_repr),
                                            (ed2.FStar_Syntax_Syntax.return_repr),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                      | uu____3875 ->
                                          let repr =
                                            let uu____3877 =
                                              FStar_Syntax_Util.type_u ()  in
                                            match uu____3877 with
                                            | (t,uu____3883) ->
                                                let expected_k =
                                                  let uu____3887 =
                                                    let uu____3896 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____3903 =
                                                      let uu____3912 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_a
                                                         in
                                                      [uu____3912]  in
                                                    uu____3896 :: uu____3903
                                                     in
                                                  let uu____3937 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____3887 uu____3937
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
                                            let uu____3954 =
                                              let uu____3961 =
                                                let uu____3962 =
                                                  let uu____3979 =
                                                    let uu____3990 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    let uu____3999 =
                                                      let uu____4010 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          wp
                                                         in
                                                      [uu____4010]  in
                                                    uu____3990 :: uu____3999
                                                     in
                                                  (repr1, uu____3979)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____3962
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____3961
                                               in
                                            uu____3954
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let mk_repr a1 wp =
                                            let uu____4068 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            mk_repr' uu____4068 wp  in
                                          let destruct_repr t =
                                            let uu____4083 =
                                              let uu____4084 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____4084.FStar_Syntax_Syntax.n
                                               in
                                            match uu____4083 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____4095,(t1,uu____4097)::
                                                 (wp,uu____4099)::[])
                                                -> (t1, wp)
                                            | uu____4158 ->
                                                failwith
                                                  "Unexpected repr type"
                                             in
                                          let bind_repr =
                                            let r =
                                              let uu____4170 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  FStar_Parser_Const.range_0
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_All.pipe_right uu____4170
                                                FStar_Syntax_Syntax.fv_to_tm
                                               in
                                            let uu____4171 =
                                              fresh_effect_signature ()  in
                                            match uu____4171 with
                                            | (b,wp_b) ->
                                                let a_wp_b =
                                                  let uu____4187 =
                                                    let uu____4196 =
                                                      let uu____4203 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____4203
                                                       in
                                                    [uu____4196]  in
                                                  let uu____4216 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      wp_b
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____4187 uu____4216
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
                                                  let uu____4224 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____4224
                                                   in
                                                let wp_g_x =
                                                  let uu____4229 =
                                                    let uu____4234 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        wp_g
                                                       in
                                                    let uu____4235 =
                                                      let uu____4236 =
                                                        let uu____4245 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____4245
                                                         in
                                                      [uu____4236]  in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____4234 uu____4235
                                                     in
                                                  uu____4229
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                let res =
                                                  let wp =
                                                    let uu____4276 =
                                                      let uu____4281 =
                                                        let uu____4282 =
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            bind_wp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4282
                                                          FStar_Pervasives_Native.snd
                                                         in
                                                      let uu____4291 =
                                                        let uu____4292 =
                                                          let uu____4295 =
                                                            let uu____4298 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a
                                                               in
                                                            let uu____4299 =
                                                              let uu____4302
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b
                                                                 in
                                                              let uu____4303
                                                                =
                                                                let uu____4306
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                   in
                                                                let uu____4307
                                                                  =
                                                                  let uu____4310
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                  [uu____4310]
                                                                   in
                                                                uu____4306 ::
                                                                  uu____4307
                                                                 in
                                                              uu____4302 ::
                                                                uu____4303
                                                               in
                                                            uu____4298 ::
                                                              uu____4299
                                                             in
                                                          r :: uu____4295  in
                                                        FStar_List.map
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____4292
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____4281 uu____4291
                                                       in
                                                    uu____4276
                                                      FStar_Pervasives_Native.None
                                                      FStar_Range.dummyRange
                                                     in
                                                  mk_repr b wp  in
                                                let maybe_range_arg =
                                                  let uu____4328 =
                                                    FStar_Util.for_some
                                                      (FStar_Syntax_Util.attr_eq
                                                         FStar_Syntax_Util.dm4f_bind_range_attr)
                                                      ed2.FStar_Syntax_Syntax.eff_attrs
                                                     in
                                                  if uu____4328
                                                  then
                                                    let uu____4339 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    let uu____4346 =
                                                      let uu____4355 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          FStar_Syntax_Syntax.t_range
                                                         in
                                                      [uu____4355]  in
                                                    uu____4339 :: uu____4346
                                                  else []  in
                                                let expected_k =
                                                  let uu____4391 =
                                                    let uu____4400 =
                                                      let uu____4409 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let uu____4416 =
                                                        let uu____4425 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            b
                                                           in
                                                        [uu____4425]  in
                                                      uu____4409 ::
                                                        uu____4416
                                                       in
                                                    let uu____4450 =
                                                      let uu____4459 =
                                                        let uu____4468 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_f
                                                           in
                                                        let uu____4475 =
                                                          let uu____4484 =
                                                            let uu____4491 =
                                                              let uu____4492
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              mk_repr a
                                                                uu____4492
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____4491
                                                             in
                                                          let uu____4493 =
                                                            let uu____4502 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_g
                                                               in
                                                            let uu____4509 =
                                                              let uu____4518
                                                                =
                                                                let uu____4525
                                                                  =
                                                                  let uu____4526
                                                                    =
                                                                    let uu____4535
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____4535]
                                                                     in
                                                                  let uu____4554
                                                                    =
                                                                    let uu____4557
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____4557
                                                                     in
                                                                  FStar_Syntax_Util.arrow
                                                                    uu____4526
                                                                    uu____4554
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____4525
                                                                 in
                                                              [uu____4518]
                                                               in
                                                            uu____4502 ::
                                                              uu____4509
                                                             in
                                                          uu____4484 ::
                                                            uu____4493
                                                           in
                                                        uu____4468 ::
                                                          uu____4475
                                                         in
                                                      FStar_List.append
                                                        maybe_range_arg
                                                        uu____4459
                                                       in
                                                    FStar_List.append
                                                      uu____4400 uu____4450
                                                     in
                                                  let uu____4602 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____4391 uu____4602
                                                   in
                                                let uu____4605 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                (match uu____4605 with
                                                 | (expected_k1,uu____4613,uu____4614)
                                                     ->
                                                     let env3 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env2
                                                         (FStar_Pervasives_Native.snd
                                                            ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                        in
                                                     let env4 =
                                                       let uu___466_4621 =
                                                         env3  in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.instantiate_imp);
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           = true;
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___466_4621.FStar_TypeChecker_Env.strict_args_tab)
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
                                              let uu____4634 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____4634
                                               in
                                            let res =
                                              let wp =
                                                let uu____4642 =
                                                  let uu____4647 =
                                                    let uu____4648 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        return_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____4648
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____4657 =
                                                    let uu____4658 =
                                                      let uu____4661 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____4662 =
                                                        let uu____4665 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        [uu____4665]  in
                                                      uu____4661 ::
                                                        uu____4662
                                                       in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____4658
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____4647 uu____4657
                                                   in
                                                uu____4642
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr a wp  in
                                            let expected_k =
                                              let uu____4677 =
                                                let uu____4686 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4693 =
                                                  let uu____4702 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x_a
                                                     in
                                                  [uu____4702]  in
                                                uu____4686 :: uu____4693  in
                                              let uu____4727 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____4677 uu____4727
                                               in
                                            let uu____4730 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            match uu____4730 with
                                            | (expected_k1,uu____4738,uu____4739)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env2
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                let uu____4745 =
                                                  check_and_gen' env3
                                                    ed2.FStar_Syntax_Syntax.return_repr
                                                    expected_k1
                                                   in
                                                (match uu____4745 with
                                                 | (univs1,repr1) ->
                                                     (match univs1 with
                                                      | [] -> ([], repr1)
                                                      | uu____4768 ->
                                                          FStar_Errors.raise_error
                                                            (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                              "Unexpected universe-polymorphic return for effect")
                                                            repr1.FStar_Syntax_Syntax.pos))
                                             in
                                          let actions =
                                            let check_action act =
                                              let uu____4783 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env2, act)
                                                else
                                                  (let uu____4797 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____4797 with
                                                   | (usubst,uvs) ->
                                                       let uu____4820 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env2 uvs
                                                          in
                                                       let uu____4821 =
                                                         let uu___495_4822 =
                                                           act  in
                                                         let uu____4823 =
                                                           FStar_Syntax_Subst.subst_binders
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_params
                                                            in
                                                         let uu____4824 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____4825 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___495_4822.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___495_4822.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             = uu____4823;
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____4824;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____4825
                                                         }  in
                                                       (uu____4820,
                                                         uu____4821))
                                                 in
                                              match uu____4783 with
                                              | (env3,act1) ->
                                                  let act_typ =
                                                    let uu____4829 =
                                                      let uu____4830 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____4830.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____4829 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____4856 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____4856
                                                        then
                                                          let uu____4859 =
                                                            let uu____4862 =
                                                              let uu____4863
                                                                =
                                                                let uu____4864
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4864
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____4863
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____4862
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs uu____4859
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____4887 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____4888 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env3 act_typ
                                                     in
                                                  (match uu____4888 with
                                                   | (act_typ1,uu____4896,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___512_4899 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env3 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___512_4899.FStar_TypeChecker_Env.strict_args_tab)
                                                         }  in
                                                       ((let uu____4902 =
                                                           FStar_TypeChecker_Env.debug
                                                             env3
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____4902
                                                         then
                                                           let uu____4906 =
                                                             FStar_Ident.text_of_lid
                                                               act1.FStar_Syntax_Syntax.action_name
                                                              in
                                                           let uu____4908 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act1.FStar_Syntax_Syntax.action_defn
                                                              in
                                                           let uu____4910 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ1
                                                              in
                                                           FStar_Util.print3
                                                             "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                             uu____4906
                                                             uu____4908
                                                             uu____4910
                                                         else ());
                                                        (let uu____4915 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____4915
                                                         with
                                                         | (act_defn,uu____4923,g_a)
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
                                                             let uu____4927 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c) ->
                                                                   let uu____4963
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____4963
                                                                    with
                                                                    | 
                                                                    (bs1,uu____4975)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____4982
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____4982
                                                                     in
                                                                    let uu____4985
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____4985
                                                                    with
                                                                    | 
                                                                    (k1,uu____4999,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____5003
                                                                   ->
                                                                   let uu____5004
                                                                    =
                                                                    let uu____5010
                                                                    =
                                                                    let uu____5012
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____5014
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____5012
                                                                    uu____5014
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____5010)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____5004
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____4927
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____5032
                                                                    =
                                                                    let uu____5033
                                                                    =
                                                                    let uu____5034
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____5034
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____5033
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____5032);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____5036
                                                                    =
                                                                    let uu____5037
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____5037.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5036
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5062
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5062
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____5069
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____5069
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____5089
                                                                    =
                                                                    let uu____5090
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____5090]
                                                                     in
                                                                    let uu____5091
                                                                    =
                                                                    let uu____5102
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____5102]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____5089;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____5091;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____5127
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____5127))
                                                                    | 
                                                                    uu____5130
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____5132
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____5154
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____5154))
                                                                     in
                                                                    match uu____5132
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
                                                                    let uu___562_5173
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___562_5173.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___562_5173.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___562_5173.FStar_Syntax_Syntax.action_params);
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
                                    (match uu____3842 with
                                     | (repr,bind_repr,return_repr,actions)
                                         ->
                                         let t0 =
                                           let uu____5197 =
                                             FStar_Syntax_Syntax.mk_Total
                                               ed2.FStar_Syntax_Syntax.signature
                                              in
                                           FStar_Syntax_Util.arrow
                                             ed2.FStar_Syntax_Syntax.binders
                                             uu____5197
                                            in
                                         let uu____5200 =
                                           let uu____5205 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env0 t0
                                              in
                                           match uu____5205 with
                                           | (gen_univs,t) ->
                                               (match annotated_univ_names
                                                with
                                                | [] -> (gen_univs, t)
                                                | uu____5224 ->
                                                    let uu____5227 =
                                                      ((FStar_List.length
                                                          gen_univs)
                                                         =
                                                         (FStar_List.length
                                                            annotated_univ_names))
                                                        &&
                                                        (FStar_List.forall2
                                                           (fun u1  ->
                                                              fun u2  ->
                                                                let uu____5234
                                                                  =
                                                                  FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2
                                                                   in
                                                                uu____5234 =
                                                                  Prims.int_zero)
                                                           gen_univs
                                                           annotated_univ_names)
                                                       in
                                                    if uu____5227
                                                    then (gen_univs, t)
                                                    else
                                                      (let uu____5245 =
                                                         let uu____5251 =
                                                           let uu____5253 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  annotated_univ_names)
                                                              in
                                                           let uu____5255 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  gen_univs)
                                                              in
                                                           FStar_Util.format2
                                                             "Expected an effect definition with %s universes; but found %s"
                                                             uu____5253
                                                             uu____5255
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                           uu____5251)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____5245
                                                         (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                            in
                                         (match uu____5200 with
                                          | (univs1,t) ->
                                              let signature1 =
                                                let uu____5266 =
                                                  let uu____5279 =
                                                    let uu____5280 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____5280.FStar_Syntax_Syntax.n
                                                     in
                                                  (effect_params, uu____5279)
                                                   in
                                                match uu____5266 with
                                                | ([],uu____5291) -> t
                                                | (uu____5306,FStar_Syntax_Syntax.Tm_arrow
                                                   (uu____5307,c)) ->
                                                    FStar_Syntax_Util.comp_result
                                                      c
                                                | uu____5345 ->
                                                    failwith
                                                      "Impossible : t is an arrow"
                                                 in
                                              let close1 n1 ts =
                                                let ts1 =
                                                  let uu____5373 =
                                                    FStar_Syntax_Subst.close_tscheme
                                                      effect_params ts
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars_tscheme
                                                    univs1 uu____5373
                                                   in
                                                let m =
                                                  FStar_List.length
                                                    (FStar_Pervasives_Native.fst
                                                       ts1)
                                                   in
                                                (let uu____5380 =
                                                   ((n1 >= Prims.int_zero) &&
                                                      (let uu____5384 =
                                                         FStar_Syntax_Util.is_unknown
                                                           (FStar_Pervasives_Native.snd
                                                              ts1)
                                                          in
                                                       Prims.op_Negation
                                                         uu____5384))
                                                     && (m <> n1)
                                                    in
                                                 if uu____5380
                                                 then
                                                   let error =
                                                     if m < n1
                                                     then
                                                       "not universe-polymorphic enough"
                                                     else
                                                       "too universe-polymorphic"
                                                      in
                                                   let err_msg =
                                                     let uu____5402 =
                                                       FStar_Util.string_of_int
                                                         m
                                                        in
                                                     let uu____5404 =
                                                       FStar_Util.string_of_int
                                                         n1
                                                        in
                                                     let uu____5406 =
                                                       FStar_Syntax_Print.tscheme_to_string
                                                         ts1
                                                        in
                                                     FStar_Util.format4
                                                       "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                       error uu____5402
                                                       uu____5404 uu____5406
                                                      in
                                                   FStar_Errors.raise_error
                                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                       err_msg)
                                                     (FStar_Pervasives_Native.snd
                                                        ts1).FStar_Syntax_Syntax.pos
                                                 else ());
                                                ts1  in
                                              let close_action act =
                                                let uu____5422 =
                                                  close1 (~- Prims.int_one)
                                                    ((act.FStar_Syntax_Syntax.action_univs),
                                                      (act.FStar_Syntax_Syntax.action_defn))
                                                   in
                                                match uu____5422 with
                                                | (univs2,defn) ->
                                                    let uu____5438 =
                                                      close1
                                                        (~- Prims.int_one)
                                                        ((act.FStar_Syntax_Syntax.action_univs),
                                                          (act.FStar_Syntax_Syntax.action_typ))
                                                       in
                                                    (match uu____5438 with
                                                     | (univs',typ) ->
                                                         let uu___612_5455 =
                                                           act  in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___612_5455.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___612_5455.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = univs2;
                                                           FStar_Syntax_Syntax.action_params
                                                             =
                                                             (uu___612_5455.FStar_Syntax_Syntax.action_params);
                                                           FStar_Syntax_Syntax.action_defn
                                                             = defn;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = typ
                                                         })
                                                 in
                                              let match_wps =
                                                let uu____5462 =
                                                  let uu____5463 =
                                                    close1 Prims.int_zero
                                                      if_then_else2
                                                     in
                                                  let uu____5465 =
                                                    close1 Prims.int_zero
                                                      ite_wp1
                                                     in
                                                  let uu____5467 =
                                                    close1 Prims.int_one
                                                      close_wp1
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.if_then_else
                                                      = uu____5463;
                                                    FStar_Syntax_Syntax.ite_wp
                                                      = uu____5465;
                                                    FStar_Syntax_Syntax.close_wp
                                                      = uu____5467
                                                  }  in
                                                FStar_Util.Inl uu____5462  in
                                              let ed3 =
                                                let uu___616_5470 = ed2  in
                                                let uu____5471 =
                                                  close1 Prims.int_zero
                                                    return_wp
                                                   in
                                                let uu____5473 =
                                                  close1 Prims.int_one
                                                    bind_wp
                                                   in
                                                let uu____5475 =
                                                  close1 Prims.int_zero
                                                    stronger
                                                   in
                                                let uu____5477 =
                                                  FStar_Util.map_opt
                                                    trivial_wp
                                                    (close1 Prims.int_zero)
                                                   in
                                                let uu____5481 =
                                                  let uu____5482 =
                                                    close1 Prims.int_zero
                                                      ([], repr)
                                                     in
                                                  FStar_Pervasives_Native.snd
                                                    uu____5482
                                                   in
                                                let uu____5500 =
                                                  close1 Prims.int_zero
                                                    return_repr
                                                   in
                                                let uu____5502 =
                                                  close1 Prims.int_one
                                                    bind_repr
                                                   in
                                                let uu____5504 =
                                                  FStar_List.map close_action
                                                    actions
                                                   in
                                                {
                                                  FStar_Syntax_Syntax.is_layered
                                                    =
                                                    (uu___616_5470.FStar_Syntax_Syntax.is_layered);
                                                  FStar_Syntax_Syntax.cattributes
                                                    =
                                                    (uu___616_5470.FStar_Syntax_Syntax.cattributes);
                                                  FStar_Syntax_Syntax.mname =
                                                    (uu___616_5470.FStar_Syntax_Syntax.mname);
                                                  FStar_Syntax_Syntax.univs =
                                                    univs1;
                                                  FStar_Syntax_Syntax.binders
                                                    = effect_params;
                                                  FStar_Syntax_Syntax.signature
                                                    = signature1;
                                                  FStar_Syntax_Syntax.ret_wp
                                                    = uu____5471;
                                                  FStar_Syntax_Syntax.bind_wp
                                                    = uu____5473;
                                                  FStar_Syntax_Syntax.stronger
                                                    = uu____5475;
                                                  FStar_Syntax_Syntax.match_wps
                                                    = match_wps;
                                                  FStar_Syntax_Syntax.trivial
                                                    = uu____5477;
                                                  FStar_Syntax_Syntax.repr =
                                                    uu____5481;
                                                  FStar_Syntax_Syntax.return_repr
                                                    = uu____5500;
                                                  FStar_Syntax_Syntax.bind_repr
                                                    = uu____5502;
                                                  FStar_Syntax_Syntax.stronger_repr
                                                    =
                                                    (uu___616_5470.FStar_Syntax_Syntax.stronger_repr);
                                                  FStar_Syntax_Syntax.actions
                                                    = uu____5504;
                                                  FStar_Syntax_Syntax.eff_attrs
                                                    =
                                                    (uu___616_5470.FStar_Syntax_Syntax.eff_attrs)
                                                }  in
                                              ((let uu____5508 =
                                                  (FStar_TypeChecker_Env.debug
                                                     env2 FStar_Options.Low)
                                                    ||
                                                    (FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env2)
                                                       (FStar_Options.Other
                                                          "ED"))
                                                   in
                                                if uu____5508
                                                then
                                                  let uu____5513 =
                                                    FStar_Syntax_Print.eff_decl_to_string
                                                      false ed3
                                                     in
                                                  FStar_Util.print_string
                                                    uu____5513
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
      let uu____5539 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____5539 with
      | (effect_binders_un,signature_un) ->
          let uu____5556 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____5556 with
           | (effect_binders,env1,uu____5575) ->
               let uu____5576 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____5576 with
                | (signature,uu____5592) ->
                    let raise_error1 uu____5608 =
                      match uu____5608 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____5644  ->
                           match uu____5644 with
                           | (bv,qual) ->
                               let uu____5663 =
                                 let uu___641_5664 = bv  in
                                 let uu____5665 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___641_5664.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___641_5664.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____5665
                                 }  in
                               (uu____5663, qual)) effect_binders
                       in
                    let uu____5670 =
                      let uu____5677 =
                        let uu____5678 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____5678.FStar_Syntax_Syntax.n  in
                      match uu____5677 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____5688)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____5720 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____5670 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____5746 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____5746
                           then
                             let uu____5749 =
                               let uu____5752 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____5752  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____5749
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____5800 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____5800 with
                           | (t2,comp,uu____5813) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____5822 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____5822 with
                          | (repr,_comp) ->
                              ((let uu____5846 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____5846
                                then
                                  let uu____5850 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____5850
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
                                let uu____5857 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____5860 =
                                    let uu____5861 =
                                      let uu____5862 =
                                        let uu____5879 =
                                          let uu____5890 =
                                            let uu____5899 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____5902 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____5899, uu____5902)  in
                                          [uu____5890]  in
                                        (wp_type, uu____5879)  in
                                      FStar_Syntax_Syntax.Tm_app uu____5862
                                       in
                                    mk1 uu____5861  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____5860
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____5950 =
                                      let uu____5957 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____5957)  in
                                    let uu____5963 =
                                      let uu____5972 =
                                        let uu____5979 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____5979
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____5972]  in
                                    uu____5950 :: uu____5963  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____6016 =
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
                                  let uu____6082 = item  in
                                  match uu____6082 with
                                  | (u_item,item1) ->
                                      let uu____6097 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____6097 with
                                       | (item2,item_comp) ->
                                           ((let uu____6113 =
                                               let uu____6115 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____6115
                                                in
                                             if uu____6113
                                             then
                                               let uu____6118 =
                                                 let uu____6124 =
                                                   let uu____6126 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____6128 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____6126 uu____6128
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____6124)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____6118
                                             else ());
                                            (let uu____6134 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____6134 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____6152 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____6154 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____6156 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____6156 with
                                | (dmff_env1,uu____6182,bind_wp,bind_elab) ->
                                    let uu____6185 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____6185 with
                                     | (dmff_env2,uu____6211,return_wp,return_elab)
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
                                           let uu____6220 =
                                             let uu____6221 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____6221.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6220 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____6279 =
                                                 let uu____6298 =
                                                   let uu____6303 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____6303
                                                    in
                                                 match uu____6298 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____6385 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____6279 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____6439 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____6439 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____6462 =
                                                          let uu____6463 =
                                                            let uu____6480 =
                                                              let uu____6491
                                                                =
                                                                let uu____6500
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____6505
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____6500,
                                                                  uu____6505)
                                                                 in
                                                              [uu____6491]
                                                               in
                                                            (wp_type,
                                                              uu____6480)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____6463
                                                           in
                                                        mk1 uu____6462  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____6541 =
                                                      let uu____6550 =
                                                        let uu____6551 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____6551
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____6550
                                                       in
                                                    (match uu____6541 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____6574
                                                           =
                                                           let error_msg =
                                                             let uu____6577 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____6579 =
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
                                                               uu____6577
                                                               uu____6579
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
                                                               ((let uu____6589
                                                                   =
                                                                   let uu____6591
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____6591
                                                                    in
                                                                 if
                                                                   uu____6589
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____6596
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
                                                                   uu____6596
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
                                                             let uu____6625 =
                                                               let uu____6630
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____6631
                                                                 =
                                                                 let uu____6632
                                                                   =
                                                                   let uu____6641
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____6641,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____6632]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____6630
                                                                 uu____6631
                                                                in
                                                             uu____6625
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____6676 =
                                                             let uu____6677 =
                                                               let uu____6686
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____6686]
                                                                in
                                                             b11 ::
                                                               uu____6677
                                                              in
                                                           let uu____6711 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____6676
                                                             uu____6711
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____6714 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____6722 =
                                             let uu____6723 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____6723.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6722 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____6781 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____6781
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____6802 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____6810 =
                                             let uu____6811 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____6811.FStar_Syntax_Syntax.n
                                              in
                                           match uu____6810 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____6845 =
                                                 let uu____6846 =
                                                   let uu____6855 =
                                                     let uu____6862 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6862
                                                      in
                                                   [uu____6855]  in
                                                 FStar_List.append uu____6846
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____6845 body what
                                           | uu____6881 ->
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
                                             (let uu____6911 =
                                                let uu____6912 =
                                                  let uu____6913 =
                                                    let uu____6930 =
                                                      let uu____6941 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____6941
                                                       in
                                                    (t, uu____6930)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6913
                                                   in
                                                mk1 uu____6912  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____6911)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____6999 = f a2  in
                                               [uu____6999]
                                           | x::xs ->
                                               let uu____7010 =
                                                 apply_last1 f xs  in
                                               x :: uu____7010
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
                                           let uu____7044 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____7044 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____7074 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____7074
                                                 then
                                                   let uu____7077 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____7077
                                                 else ());
                                                (let uu____7082 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____7082))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____7091 =
                                                 let uu____7096 = mk_lid name
                                                    in
                                                 let uu____7097 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____7096 uu____7097
                                                  in
                                               (match uu____7091 with
                                                | (sigelt,fv) ->
                                                    ((let uu____7101 =
                                                        let uu____7104 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____7104
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____7101);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____7158 =
                                             let uu____7161 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____7164 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____7161 :: uu____7164  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____7158);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____7216 =
                                              let uu____7219 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____7220 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____7219 :: uu____7220  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____7216);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____7272 =
                                               let uu____7275 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____7278 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____7275 :: uu____7278  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____7272);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____7330 =
                                                let uu____7333 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____7334 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____7333 :: uu____7334  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____7330);
                                             (let uu____7383 =
                                                FStar_List.fold_left
                                                  (fun uu____7423  ->
                                                     fun action  ->
                                                       match uu____7423 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____7444 =
                                                             let uu____7451 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____7451
                                                               params_un
                                                              in
                                                           (match uu____7444
                                                            with
                                                            | (action_params,env',uu____7460)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____7486
                                                                     ->
                                                                    match uu____7486
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____7505
                                                                    =
                                                                    let uu___834_7506
                                                                    = bv  in
                                                                    let uu____7507
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___834_7506.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___834_7506.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____7507
                                                                    }  in
                                                                    (uu____7505,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____7513
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____7513
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
                                                                    uu____7552
                                                                    ->
                                                                    let uu____7553
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____7553
                                                                     in
                                                                    ((
                                                                    let uu____7557
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____7557
                                                                    then
                                                                    let uu____7562
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____7565
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____7568
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____7570
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____7562
                                                                    uu____7565
                                                                    uu____7568
                                                                    uu____7570
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
                                                                    let uu____7579
                                                                    =
                                                                    let uu____7582
                                                                    =
                                                                    let uu___856_7583
                                                                    = action
                                                                     in
                                                                    let uu____7584
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____7585
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___856_7583.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___856_7583.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___856_7583.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____7584;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____7585
                                                                    }  in
                                                                    uu____7582
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____7579))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____7383 with
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
                                                      let uu____7629 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____7636 =
                                                        let uu____7645 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____7645]  in
                                                      uu____7629 ::
                                                        uu____7636
                                                       in
                                                    let uu____7670 =
                                                      let uu____7673 =
                                                        let uu____7674 =
                                                          let uu____7675 =
                                                            let uu____7692 =
                                                              let uu____7703
                                                                =
                                                                let uu____7712
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____7715
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____7712,
                                                                  uu____7715)
                                                                 in
                                                              [uu____7703]
                                                               in
                                                            (repr,
                                                              uu____7692)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____7675
                                                           in
                                                        mk1 uu____7674  in
                                                      let uu____7751 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____7673
                                                        uu____7751
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____7670
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____7752 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____7756 =
                                                    let uu____7765 =
                                                      let uu____7766 =
                                                        let uu____7769 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____7769
                                                         in
                                                      uu____7766.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____7765 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____7783)
                                                        ->
                                                        let uu____7820 =
                                                          let uu____7841 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____7841
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____7909 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____7820
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____7974 =
                                                               let uu____7975
                                                                 =
                                                                 let uu____7978
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____7978
                                                                  in
                                                               uu____7975.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____7974
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____8011
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____8011
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____8026
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____8057
                                                                     ->
                                                                    match uu____8057
                                                                    with
                                                                    | 
                                                                    (bv,uu____8066)
                                                                    ->
                                                                    let uu____8071
                                                                    =
                                                                    let uu____8073
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____8073
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____8071
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____8026
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
                                                                    let uu____8165
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____8165
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____8175
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____8186
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____8186
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____8196
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____8199
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____8196,
                                                                    uu____8199)))
                                                              | uu____8214 ->
                                                                  let uu____8215
                                                                    =
                                                                    let uu____8221
                                                                    =
                                                                    let uu____8223
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____8223
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____8221)
                                                                     in
                                                                  raise_error1
                                                                    uu____8215))
                                                    | uu____8235 ->
                                                        let uu____8236 =
                                                          let uu____8242 =
                                                            let uu____8244 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____8244
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____8242)
                                                           in
                                                        raise_error1
                                                          uu____8236
                                                     in
                                                  (match uu____7756 with
                                                   | (pre,post) ->
                                                       ((let uu____8277 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____8280 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____8283 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___912_8286
                                                             = ed  in
                                                           let uu____8287 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____8288 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____8289 =
                                                             let uu____8290 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____8290)
                                                              in
                                                           let uu____8297 =
                                                             let uu____8298 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____8298)
                                                              in
                                                           let uu____8305 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____8306 =
                                                             let uu____8307 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____8307)
                                                              in
                                                           let uu____8314 =
                                                             let uu____8315 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____8315)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.is_layered
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.is_layered);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____8287;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____8288;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____8289;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____8297;
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.match_wps
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.match_wps);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____8305;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____8306;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____8314;
                                                             FStar_Syntax_Syntax.stronger_repr
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.stronger_repr);
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___912_8286.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____8322 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____8322
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____8340
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____8340
                                                               then
                                                                 let uu____8344
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____8344
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
                                                                    let uu____8364
                                                                    =
                                                                    let uu____8367
                                                                    =
                                                                    let uu____8368
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____8368)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____8367
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
                                                                    uu____8364;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____8375
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____8375
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____8378
                                                                 =
                                                                 let uu____8381
                                                                   =
                                                                   let uu____8384
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____8384
                                                                    in
                                                                 FStar_List.append
                                                                   uu____8381
                                                                   sigelts'
                                                                  in
                                                               (uu____8378,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____8425 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____8425 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____8460 = FStar_List.hd ses  in
            uu____8460.FStar_Syntax_Syntax.sigrng  in
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
           | uu____8465 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____8471,[],t,uu____8473,uu____8474);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____8476;
               FStar_Syntax_Syntax.sigattrs = uu____8477;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____8479,_t_top,_lex_t_top,_8513,uu____8482);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____8484;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____8485;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____8487,_t_cons,_lex_t_cons,_8521,uu____8490);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____8492;
                 FStar_Syntax_Syntax.sigattrs = uu____8493;_}::[]
               when
               ((_8513 = Prims.int_zero) && (_8521 = Prims.int_zero)) &&
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
                 let uu____8546 =
                   let uu____8553 =
                     let uu____8554 =
                       let uu____8561 =
                         let uu____8564 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____8564
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____8561, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____8554  in
                   FStar_Syntax_Syntax.mk uu____8553  in
                 uu____8546 FStar_Pervasives_Native.None r1  in
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
                   let uu____8579 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8579
                    in
                 let hd1 =
                   let uu____8581 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8581
                    in
                 let tl1 =
                   let uu____8583 =
                     let uu____8584 =
                       let uu____8591 =
                         let uu____8592 =
                           let uu____8599 =
                             let uu____8602 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____8602
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____8599, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____8592  in
                       FStar_Syntax_Syntax.mk uu____8591  in
                     uu____8584 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____8583
                    in
                 let res =
                   let uu____8608 =
                     let uu____8615 =
                       let uu____8616 =
                         let uu____8623 =
                           let uu____8626 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____8626
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____8623,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____8616  in
                     FStar_Syntax_Syntax.mk uu____8615  in
                   uu____8608 FStar_Pervasives_Native.None r2  in
                 let uu____8629 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____8629
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
               let uu____8668 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____8668;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____8673 ->
               let err_msg =
                 let uu____8678 =
                   let uu____8680 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____8680  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____8678
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
    fun uu____8705  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____8705 with
          | (uvs,t) ->
              let uu____8718 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____8718 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____8730 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____8730 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____8748 =
                        let uu____8751 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____8751
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____8748)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8774 =
          let uu____8775 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8775 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8774 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____8800 =
          let uu____8801 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____8801 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____8800 r
  
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
          (let uu____8850 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____8850
           then
             let uu____8853 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____8853
           else ());
          (let uu____8858 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____8858 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____8889 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____8889 FStar_List.flatten  in
               ((let uu____8903 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____8906 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____8906)
                    in
                 if uu____8903
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
                           let uu____8922 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____8932,uu____8933,uu____8934,uu____8935,uu____8936)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____8945 -> failwith "Impossible!"  in
                           match uu____8922 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____8964 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____8974,uu____8975,ty_lid,uu____8977,uu____8978)
                               -> (data_lid, ty_lid)
                           | uu____8985 -> failwith "Impossible"  in
                         match uu____8964 with
                         | (data_lid,ty_lid) ->
                             let uu____8993 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____8996 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____8996)
                                in
                             if uu____8993
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____9010 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9015,uu____9016,uu____9017,uu____9018,uu____9019)
                         -> lid
                     | uu____9028 -> failwith "Impossible"  in
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
                   let uu____9046 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____9046
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
          let pop1 uu____9121 =
            let uu____9122 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1090_9132  ->
               match () with
               | () ->
                   let uu____9139 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____9139 (fun r  -> pop1 (); r)) ()
          with | uu___1089_9170 -> (pop1 (); FStar_Exn.raise uu___1089_9170)
  
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
      | uu____9486 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____9544 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____9544 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____9569 .
    'Auu____9569 FStar_Pervasives_Native.option -> 'Auu____9569 Prims.list
  =
  fun uu___0_9578  ->
    match uu___0_9578 with
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
            let uu____9658 = collect1 tl1  in
            (match uu____9658 with
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
        | ((e,n1)::uu____9896,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____9952) ->
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
          let uu____10162 =
            let uu____10164 = FStar_Options.ide ()  in
            Prims.op_Negation uu____10164  in
          if uu____10162
          then
            let uu____10167 =
              let uu____10172 = FStar_TypeChecker_Env.dsenv env  in
              let uu____10173 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____10172 uu____10173  in
            (match uu____10167 with
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
                              let uu____10206 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____10207 =
                                let uu____10213 =
                                  let uu____10215 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____10217 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____10215 uu____10217
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____10213)
                                 in
                              FStar_Errors.log_issue uu____10206 uu____10207
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____10224 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____10225 =
                                   let uu____10231 =
                                     let uu____10233 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____10233
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____10231)
                                    in
                                 FStar_Errors.log_issue uu____10224
                                   uu____10225)
                              else ())
                         else ())))
          else ()
      | uu____10243 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____10288 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____10316 ->
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
             let uu____10376 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10376
             then
               let ses1 =
                 let uu____10384 =
                   let uu____10385 =
                     let uu____10386 =
                       tc_inductive
                         (let uu___1222_10395 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1222_10395.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1222_10395.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1222_10395.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1222_10395.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1222_10395.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1222_10395.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1222_10395.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1222_10395.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1222_10395.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1222_10395.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1222_10395.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1222_10395.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1222_10395.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1222_10395.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1222_10395.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1222_10395.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1222_10395.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1222_10395.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1222_10395.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1222_10395.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1222_10395.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1222_10395.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1222_10395.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1222_10395.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1222_10395.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1222_10395.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1222_10395.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1222_10395.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1222_10395.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1222_10395.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1222_10395.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1222_10395.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1222_10395.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1222_10395.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1222_10395.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1222_10395.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1222_10395.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1222_10395.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1222_10395.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1222_10395.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1222_10395.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1222_10395.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____10386
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____10385
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____10384
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____10409 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____10409
                 then
                   let uu____10414 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1226_10418 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1226_10418.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1226_10418.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1226_10418.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1226_10418.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____10414
                 else ());
                ses1)
             else ses  in
           let uu____10428 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____10428 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1233_10452 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1233_10452.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1233_10452.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1233_10452.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1233_10452.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____10464 = cps_and_elaborate env ne  in
           (match uu____10464 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1247_10503 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1247_10503.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1247_10503.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1247_10503.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1247_10503.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1250_10505 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1250_10505.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1250_10505.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1250_10505.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1250_10505.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____10512 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____10512
             then
               let uu____10517 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____10517
             else ());
            if ne.FStar_Syntax_Syntax.is_layered
            then (let uu____10524 = tc_layered_eff_decl env ne  in ())
            else ();
            (let ne1 =
               let uu____10528 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____10528
               then
                 let ne1 =
                   let uu____10532 =
                     let uu____10533 =
                       let uu____10534 =
                         tc_eff_decl
                           (let uu___1261_10537 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1261_10537.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1261_10537.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1261_10537.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1261_10537.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1261_10537.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1261_10537.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1261_10537.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1261_10537.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1261_10537.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1261_10537.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1261_10537.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1261_10537.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1261_10537.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1261_10537.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1261_10537.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1261_10537.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1261_10537.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1261_10537.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1261_10537.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1261_10537.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1261_10537.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1261_10537.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1261_10537.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1261_10537.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1261_10537.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1261_10537.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1261_10537.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1261_10537.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1261_10537.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1261_10537.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1261_10537.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1261_10537.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1261_10537.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1261_10537.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1261_10537.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1261_10537.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1261_10537.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1261_10537.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1261_10537.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1261_10537.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1261_10537.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1261_10537.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____10534
                         (fun ne1  ->
                            let uu___1264_10543 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1264_10543.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1264_10543.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1264_10543.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1264_10543.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____10533
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____10532
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____10545 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____10545
                   then
                     let uu____10550 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1268_10554 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1268_10554.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1268_10554.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1268_10554.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1268_10554.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____10550
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_eff_decl env ne1  in
             let se1 =
               let uu___1273_10562 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1273_10562.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1273_10562.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1273_10562.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1273_10562.FStar_Syntax_Syntax.sigattrs)
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
           let uu____10570 =
             let uu____10577 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____10577
              in
           (match uu____10570 with
            | (a,wp_a_src) ->
                let uu____10594 =
                  let uu____10601 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____10601
                   in
                (match uu____10594 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____10619 =
                         let uu____10622 =
                           let uu____10623 =
                             let uu____10630 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____10630)  in
                           FStar_Syntax_Syntax.NT uu____10623  in
                         [uu____10622]  in
                       FStar_Syntax_Subst.subst uu____10619 wp_b_tgt  in
                     let expected_k =
                       let uu____10638 =
                         let uu____10647 = FStar_Syntax_Syntax.mk_binder a
                            in
                         let uu____10654 =
                           let uu____10663 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____10663]  in
                         uu____10647 :: uu____10654  in
                       let uu____10688 =
                         FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                       FStar_Syntax_Util.arrow uu____10638 uu____10688  in
                     let repr_type eff_name a1 wp =
                       (let uu____10710 =
                          let uu____10712 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____10712  in
                        if uu____10710
                        then
                          let uu____10715 =
                            let uu____10721 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____10721)
                             in
                          let uu____10725 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____10715 uu____10725
                        else ());
                       (let uu____10728 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____10728 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([], (ed.FStar_Syntax_Syntax.repr))
                               in
                            let uu____10765 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____10766 =
                              let uu____10773 =
                                let uu____10774 =
                                  let uu____10791 =
                                    let uu____10802 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____10811 =
                                      let uu____10822 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____10822]  in
                                    uu____10802 :: uu____10811  in
                                  (repr, uu____10791)  in
                                FStar_Syntax_Syntax.Tm_app uu____10774  in
                              FStar_Syntax_Syntax.mk uu____10773  in
                            uu____10766 FStar_Pervasives_Native.None
                              uu____10765)
                        in
                     let uu____10867 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____11040 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____11051 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____11051 with
                               | (usubst,uvs1) ->
                                   let uu____11074 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____11075 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____11074, uu____11075)
                             else (env, lift_wp)  in
                           (match uu____11040 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____11125 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____11125))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____11196 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____11211 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____11211 with
                               | (usubst,uvs) ->
                                   let uu____11236 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____11236)
                             else ([], lift)  in
                           (match uu____11196 with
                            | (uvs,lift1) ->
                                ((let uu____11272 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____11272
                                  then
                                    let uu____11276 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____11276
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____11282 =
                                    let uu____11289 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____11289 lift1
                                     in
                                  match uu____11282 with
                                  | (lift2,comp,uu____11314) ->
                                      let uu____11315 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____11315 with
                                       | (uu____11344,lift_wp,lift_elab) ->
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
                                             let uu____11376 =
                                               let uu____11387 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____11387
                                                in
                                             let uu____11404 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____11376, uu____11404)
                                           else
                                             (let uu____11433 =
                                                let uu____11444 =
                                                  let uu____11453 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____11453)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____11444
                                                 in
                                              let uu____11468 =
                                                let uu____11477 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____11477)  in
                                              (uu____11433, uu____11468))))))
                        in
                     (match uu____10867 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1349_11551 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1349_11551.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1349_11551.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1349_11551.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1349_11551.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1349_11551.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1349_11551.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1349_11551.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1349_11551.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1349_11551.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1349_11551.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1349_11551.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1349_11551.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1349_11551.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1349_11551.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1349_11551.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1349_11551.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1349_11551.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1349_11551.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1349_11551.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1349_11551.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1349_11551.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1349_11551.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1349_11551.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1349_11551.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1349_11551.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1349_11551.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1349_11551.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1349_11551.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1349_11551.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1349_11551.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1349_11551.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1349_11551.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1349_11551.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1349_11551.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1349_11551.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1349_11551.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1349_11551.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1349_11551.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1349_11551.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1349_11551.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1349_11551.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1349_11551.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1349_11551.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____11608 =
                                  let uu____11613 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____11613 with
                                  | (usubst,uvs1) ->
                                      let uu____11636 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____11637 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____11636, uu____11637)
                                   in
                                (match uu____11608 with
                                 | (env2,lift2) ->
                                     let uu____11650 =
                                       let uu____11657 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____11657
                                        in
                                     (match uu____11650 with
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
                                              let uu____11691 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____11692 =
                                                let uu____11699 =
                                                  let uu____11700 =
                                                    let uu____11717 =
                                                      let uu____11728 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____11737 =
                                                        let uu____11748 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____11748]  in
                                                      uu____11728 ::
                                                        uu____11737
                                                       in
                                                    (lift_wp1, uu____11717)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11700
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____11699
                                                 in
                                              uu____11692
                                                FStar_Pervasives_Native.None
                                                uu____11691
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____11796 =
                                              let uu____11805 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____11812 =
                                                let uu____11821 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____11828 =
                                                  let uu____11837 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____11837]  in
                                                uu____11821 :: uu____11828
                                                 in
                                              uu____11805 :: uu____11812  in
                                            let uu____11868 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____11796 uu____11868
                                             in
                                          let uu____11871 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____11871 with
                                           | (expected_k2,uu____11889,uu____11890)
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
                                                    let uu____11914 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____11914))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____11930 =
                              let uu____11932 =
                                let uu____11934 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____11934
                                  FStar_List.length
                                 in
                              uu____11932 <> Prims.int_one  in
                            if uu____11930
                            then
                              let uu____11956 =
                                let uu____11962 =
                                  let uu____11964 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____11966 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____11968 =
                                    let uu____11970 =
                                      let uu____11972 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11972
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____11970
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____11964 uu____11966 uu____11968
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____11962)
                                 in
                              FStar_Errors.raise_error uu____11956 r
                            else ());
                           (let uu____11999 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____12010 =
                                   let uu____12012 =
                                     let uu____12015 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____12015
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____12012
                                     FStar_List.length
                                    in
                                 uu____12010 <> Prims.int_one)
                               in
                            if uu____11999
                            then
                              let uu____12070 =
                                let uu____12076 =
                                  let uu____12078 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____12080 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____12082 =
                                    let uu____12084 =
                                      let uu____12086 =
                                        let uu____12089 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____12089
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____12086
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____12084
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____12078 uu____12080 uu____12082
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____12076)
                                 in
                              FStar_Errors.raise_error uu____12070 r
                            else ());
                           (let sub2 =
                              let uu___1386_12148 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1386_12148.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1386_12148.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1389_12150 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1389_12150.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1389_12150.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1389_12150.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1389_12150.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____12164 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____12192 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____12192 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____12223 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____12223 c  in
                    let uu____12232 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____12232, uvs1, tps1, c1))
              in
           (match uu____12164 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____12254 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____12254 with
                 | (tps2,c2) ->
                     let uu____12271 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____12271 with
                      | (tps3,env3,us) ->
                          let uu____12291 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____12291 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____12319)::uu____12320 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____12339 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____12347 =
                                   let uu____12349 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____12349  in
                                 if uu____12347
                                 then
                                   let uu____12352 =
                                     let uu____12358 =
                                       let uu____12360 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____12362 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____12360 uu____12362
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____12358)
                                      in
                                   FStar_Errors.raise_error uu____12352 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____12370 =
                                   let uu____12371 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____12371
                                    in
                                 match uu____12370 with
                                 | (uvs2,t) ->
                                     let uu____12402 =
                                       let uu____12407 =
                                         let uu____12420 =
                                           let uu____12421 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____12421.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____12420)  in
                                       match uu____12407 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____12436,c5)) -> ([], c5)
                                       | (uu____12478,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____12517 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____12402 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____12551 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____12551 with
                                              | (uu____12556,t1) ->
                                                  let uu____12558 =
                                                    let uu____12564 =
                                                      let uu____12566 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____12568 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____12572 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____12566
                                                        uu____12568
                                                        uu____12572
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____12564)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____12558 r)
                                           else ();
                                           (let se1 =
                                              let uu___1459_12579 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1459_12579.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1459_12579.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1459_12579.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1459_12579.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____12586,uu____12587,uu____12588) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_12593  ->
                   match uu___1_12593 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____12596 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____12602,uu____12603) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_12612  ->
                   match uu___1_12612 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____12615 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____12626 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____12626
             then
               let uu____12629 =
                 let uu____12635 =
                   let uu____12637 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____12637
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____12635)
                  in
               FStar_Errors.raise_error uu____12629 r
             else ());
            (let uu____12643 =
               let uu____12652 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____12652
               then
                 let uu____12663 =
                   tc_declare_typ
                     (let uu___1483_12666 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1483_12666.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1483_12666.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1483_12666.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1483_12666.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1483_12666.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1483_12666.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1483_12666.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1483_12666.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1483_12666.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1483_12666.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1483_12666.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1483_12666.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1483_12666.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1483_12666.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1483_12666.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1483_12666.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1483_12666.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1483_12666.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1483_12666.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1483_12666.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1483_12666.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1483_12666.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1483_12666.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1483_12666.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1483_12666.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1483_12666.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1483_12666.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1483_12666.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1483_12666.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1483_12666.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1483_12666.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1483_12666.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1483_12666.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1483_12666.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1483_12666.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1483_12666.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1483_12666.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1483_12666.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1483_12666.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1483_12666.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1483_12666.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1483_12666.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1483_12666.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____12663 with
                 | (uvs1,t1) ->
                     ((let uu____12691 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____12691
                       then
                         let uu____12696 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____12698 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____12696 uu____12698
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____12643 with
             | (uvs1,t1) ->
                 let uu____12733 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____12733 with
                  | (uvs2,t2) ->
                      ([(let uu___1496_12763 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1496_12763.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1496_12763.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1496_12763.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1496_12763.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____12768 =
             let uu____12777 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____12777
             then
               let uu____12788 =
                 tc_assume
                   (let uu___1505_12791 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1505_12791.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1505_12791.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1505_12791.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1505_12791.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1505_12791.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1505_12791.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1505_12791.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1505_12791.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1505_12791.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1505_12791.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1505_12791.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1505_12791.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1505_12791.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1505_12791.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1505_12791.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1505_12791.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1505_12791.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1505_12791.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1505_12791.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1505_12791.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1505_12791.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1505_12791.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1505_12791.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1505_12791.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1505_12791.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1505_12791.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1505_12791.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1505_12791.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1505_12791.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1505_12791.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1505_12791.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1505_12791.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1505_12791.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1505_12791.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1505_12791.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1505_12791.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1505_12791.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1505_12791.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1505_12791.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1505_12791.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1505_12791.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1505_12791.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____12788 with
               | (uvs1,t1) ->
                   ((let uu____12817 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____12817
                     then
                       let uu____12822 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12824 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____12822
                         uu____12824
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____12768 with
            | (uvs1,t1) ->
                let uu____12859 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____12859 with
                 | (uvs2,t2) ->
                     ([(let uu___1518_12889 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1518_12889.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1518_12889.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1518_12889.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1518_12889.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____12893 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____12893 with
            | (e1,c,g1) ->
                let uu____12913 =
                  let uu____12920 =
                    let uu____12923 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____12923  in
                  let uu____12924 =
                    let uu____12929 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____12929)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____12920 uu____12924
                   in
                (match uu____12913 with
                 | (e2,uu____12941,g) ->
                     ((let uu____12944 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____12944);
                      (let se1 =
                         let uu___1533_12946 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1533_12946.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1533_12946.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1533_12946.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1533_12946.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____12958 = FStar_Options.debug_any ()  in
             if uu____12958
             then
               let uu____12961 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____12963 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____12961
                 uu____12963
             else ());
            (let uu____12968 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____12968 with
             | (t1,uu____12986,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____13000 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____13000 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____13003 =
                              let uu____13009 =
                                let uu____13011 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____13013 =
                                  let uu____13015 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____13015
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____13011 uu____13013
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____13009)
                               in
                            FStar_Errors.raise_error uu____13003 r
                        | uu____13027 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1554_13032 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1554_13032.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1554_13032.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1554_13032.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1554_13032.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1554_13032.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1554_13032.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1554_13032.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1554_13032.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1554_13032.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1554_13032.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1554_13032.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1554_13032.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1554_13032.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1554_13032.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1554_13032.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1554_13032.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1554_13032.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1554_13032.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1554_13032.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1554_13032.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1554_13032.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1554_13032.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1554_13032.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1554_13032.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1554_13032.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1554_13032.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1554_13032.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1554_13032.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1554_13032.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1554_13032.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1554_13032.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1554_13032.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1554_13032.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1554_13032.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1554_13032.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1554_13032.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1554_13032.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1554_13032.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1554_13032.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1554_13032.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1554_13032.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1554_13032.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1554_13032.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____13100 =
                   let uu____13102 =
                     let uu____13111 = drop_logic val_q  in
                     let uu____13114 = drop_logic q'  in
                     (uu____13111, uu____13114)  in
                   match uu____13102 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____13100
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____13141 =
                      let uu____13147 =
                        let uu____13149 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____13151 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____13153 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____13149 uu____13151 uu____13153
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____13147)
                       in
                    FStar_Errors.raise_error uu____13141 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____13190 =
                   let uu____13191 = FStar_Syntax_Subst.compress def  in
                   uu____13191.FStar_Syntax_Syntax.n  in
                 match uu____13190 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____13203,uu____13204) -> binders
                 | uu____13229 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____13241;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____13346) -> val_bs1
                     | (uu____13377,[]) -> val_bs1
                     | ((body_bv,uu____13409)::bt,(val_bv,aqual)::vt) ->
                         let uu____13466 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____13490) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1623_13504 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1625_13507 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1625_13507.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1623_13504.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1623_13504.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____13466
                      in
                   let uu____13514 =
                     let uu____13521 =
                       let uu____13522 =
                         let uu____13537 = rename_binders1 def_bs val_bs  in
                         (uu____13537, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____13522  in
                     FStar_Syntax_Syntax.mk uu____13521  in
                   uu____13514 FStar_Pervasives_Native.None r1
               | uu____13556 -> typ1  in
             let uu___1631_13557 = lb  in
             let uu____13558 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1631_13557.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1631_13557.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____13558;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1631_13557.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1631_13557.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1631_13557.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1631_13557.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____13561 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____13616  ->
                     fun lb  ->
                       match uu____13616 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____13662 =
                             let uu____13674 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____13674 with
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
                                   | uu____13754 ->
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
                                  (let uu____13801 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____13801, quals_opt1)))
                              in
                           (match uu____13662 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____13561 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____13905 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_13911  ->
                                match uu___2_13911 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____13916 -> false))
                         in
                      if uu____13905
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____13929 =
                    let uu____13936 =
                      let uu____13937 =
                        let uu____13951 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____13951)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____13937  in
                    FStar_Syntax_Syntax.mk uu____13936  in
                  uu____13929 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1674_13970 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1674_13970.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1674_13970.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1674_13970.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1674_13970.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1674_13970.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1674_13970.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1674_13970.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1674_13970.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1674_13970.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1674_13970.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1674_13970.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1674_13970.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1674_13970.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1674_13970.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1674_13970.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1674_13970.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1674_13970.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1674_13970.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1674_13970.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1674_13970.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1674_13970.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1674_13970.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1674_13970.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1674_13970.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1674_13970.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1674_13970.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1674_13970.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1674_13970.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1674_13970.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1674_13970.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1674_13970.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1674_13970.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1674_13970.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1674_13970.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1674_13970.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1674_13970.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1674_13970.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1674_13970.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1674_13970.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1674_13970.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1674_13970.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1674_13970.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____13973 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____13973
                  then
                    let drop_lbtyp e_lax =
                      let uu____13982 =
                        let uu____13983 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____13983.FStar_Syntax_Syntax.n  in
                      match uu____13982 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____14005 =
                              let uu____14006 = FStar_Syntax_Subst.compress e
                                 in
                              uu____14006.FStar_Syntax_Syntax.n  in
                            match uu____14005 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____14010,lb1::[]),uu____14012) ->
                                let uu____14028 =
                                  let uu____14029 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____14029.FStar_Syntax_Syntax.n  in
                                (match uu____14028 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____14034 -> false)
                            | uu____14036 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1699_14040 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1701_14055 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1701_14055.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1701_14055.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1701_14055.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1701_14055.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1701_14055.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1701_14055.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1699_14040.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1699_14040.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____14058 -> e_lax  in
                    let uu____14059 =
                      FStar_Util.record_time
                        (fun uu____14067  ->
                           let uu____14068 =
                             let uu____14069 =
                               let uu____14070 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1705_14079 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1705_14079.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1705_14079.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1705_14079.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1705_14079.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1705_14079.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1705_14079.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1705_14079.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1705_14079.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1705_14079.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1705_14079.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1705_14079.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1705_14079.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1705_14079.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1705_14079.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1705_14079.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1705_14079.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1705_14079.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1705_14079.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1705_14079.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1705_14079.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1705_14079.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1705_14079.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1705_14079.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1705_14079.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1705_14079.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1705_14079.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1705_14079.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1705_14079.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1705_14079.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1705_14079.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1705_14079.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1705_14079.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1705_14079.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1705_14079.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1705_14079.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1705_14079.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1705_14079.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1705_14079.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1705_14079.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1705_14079.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1705_14079.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1705_14079.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____14070
                                 (fun uu____14092  ->
                                    match uu____14092 with
                                    | (e1,uu____14100,uu____14101) -> e1)
                                in
                             FStar_All.pipe_right uu____14069
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____14068 drop_lbtyp)
                       in
                    match uu____14059 with
                    | (e1,ms) ->
                        ((let uu____14107 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____14107
                          then
                            let uu____14112 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____14112
                          else ());
                         (let uu____14118 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____14118
                          then
                            let uu____14123 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____14123
                          else ());
                         e1)
                  else e  in
                let uu____14130 =
                  let uu____14139 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____14139 with
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
                (match uu____14130 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1735_14244 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1735_14244.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1735_14244.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1735_14244.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1735_14244.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1742_14257 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1742_14257.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1742_14257.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1742_14257.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1742_14257.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1742_14257.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1742_14257.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____14258 =
                       FStar_Util.record_time
                         (fun uu____14277  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____14258 with
                      | (r1,ms) ->
                          ((let uu____14305 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____14305
                            then
                              let uu____14310 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____14310
                            else ());
                           (let uu____14315 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____14340;
                                   FStar_Syntax_Syntax.vars = uu____14341;_},uu____14342,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____14372 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____14372)
                                     in
                                  let lbs3 =
                                    let uu____14396 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____14396)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____14419,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____14424 -> quals  in
                                  ((let uu___1772_14433 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1772_14433.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1772_14433.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1772_14433.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____14436 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____14315 with
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
                                 (let uu____14492 = log env1  in
                                  if uu____14492
                                  then
                                    let uu____14495 =
                                      let uu____14497 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____14517 =
                                                    let uu____14526 =
                                                      let uu____14527 =
                                                        let uu____14530 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____14530.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____14527.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____14526
                                                     in
                                                  match uu____14517 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____14539 -> false  in
                                                if should_log
                                                then
                                                  let uu____14551 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____14553 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____14551
                                                    uu____14553
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____14497
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____14495
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
      (let uu____14605 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____14605
       then
         let uu____14608 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____14608
       else ());
      (let uu____14613 = get_fail_se se  in
       match uu____14613 with
       | FStar_Pervasives_Native.Some (uu____14634,false ) when
           let uu____14651 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____14651 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1803_14677 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1803_14677.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1803_14677.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1803_14677.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1803_14677.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1803_14677.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1803_14677.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1803_14677.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1803_14677.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1803_14677.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1803_14677.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1803_14677.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1803_14677.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1803_14677.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1803_14677.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1803_14677.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1803_14677.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1803_14677.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1803_14677.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1803_14677.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1803_14677.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1803_14677.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1803_14677.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1803_14677.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1803_14677.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1803_14677.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1803_14677.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1803_14677.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1803_14677.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1803_14677.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1803_14677.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1803_14677.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1803_14677.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1803_14677.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1803_14677.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1803_14677.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1803_14677.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1803_14677.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1803_14677.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1803_14677.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1803_14677.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1803_14677.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1803_14677.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1803_14677.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____14682 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____14682
             then
               let uu____14685 =
                 let uu____14687 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____14687
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____14685
             else ());
            (let uu____14701 =
               FStar_Errors.catch_errors
                 (fun uu____14731  ->
                    FStar_Options.with_saved_options
                      (fun uu____14743  -> tc_decl' env' se))
                in
             match uu____14701 with
             | (errs,uu____14755) ->
                 ((let uu____14785 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____14785
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____14820 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____14820  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____14832 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____14843 =
                            let uu____14853 = check_multi_eq errnos1 actual
                               in
                            match uu____14853 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____14843 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____14918 =
                                   let uu____14924 =
                                     let uu____14926 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____14929 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____14932 =
                                       FStar_Util.string_of_int e  in
                                     let uu____14934 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____14936 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____14926 uu____14929 uu____14932
                                       uu____14934 uu____14936
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____14924)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____14918)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____14963 .
    'Auu____14963 ->
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
               (fun uu___3_15006  ->
                  match uu___3_15006 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____15009 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____15020) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____15028 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____15038 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____15043 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____15059 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____15085 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15111) ->
            let uu____15120 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____15120
            then
              let for_export_bundle se1 uu____15157 =
                match uu____15157 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____15196,uu____15197) ->
                         let dec =
                           let uu___1879_15207 = se1  in
                           let uu____15208 =
                             let uu____15209 =
                               let uu____15216 =
                                 let uu____15217 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____15217  in
                               (l, us, uu____15216)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____15209
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____15208;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1879_15207.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1879_15207.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1879_15207.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____15227,uu____15228,uu____15229) ->
                         let dec =
                           let uu___1890_15237 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___1890_15237.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___1890_15237.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___1890_15237.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____15242 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____15265,uu____15266,uu____15267) ->
            let uu____15268 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____15268 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____15292 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____15292
            then
              ([(let uu___1906_15311 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___1906_15311.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___1906_15311.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___1906_15311.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____15314 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_15320  ->
                         match uu___4_15320 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____15323 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____15329 ->
                             true
                         | uu____15331 -> false))
                  in
               if uu____15314 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____15352 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____15357 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15362 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____15367 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15372 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____15390) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____15404 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____15404
            then ([], hidden)
            else
              (let dec =
                 let uu____15425 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____15425;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____15436 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____15436
            then
              let uu____15447 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1943_15461 = se  in
                        let uu____15462 =
                          let uu____15463 =
                            let uu____15470 =
                              let uu____15471 =
                                let uu____15474 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____15474.FStar_Syntax_Syntax.fv_name  in
                              uu____15471.FStar_Syntax_Syntax.v  in
                            (uu____15470, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____15463  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____15462;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1943_15461.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1943_15461.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1943_15461.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____15447, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____15497 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____15497
       then
         let uu____15500 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____15500
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____15505 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____15523 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____15540) ->
           let env1 =
             let uu___1964_15545 = env  in
             let uu____15546 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1964_15545.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1964_15545.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1964_15545.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1964_15545.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1964_15545.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1964_15545.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1964_15545.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1964_15545.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1964_15545.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1964_15545.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1964_15545.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1964_15545.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1964_15545.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1964_15545.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1964_15545.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1964_15545.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1964_15545.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1964_15545.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1964_15545.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1964_15545.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1964_15545.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1964_15545.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1964_15545.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1964_15545.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1964_15545.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1964_15545.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1964_15545.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1964_15545.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1964_15545.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1964_15545.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1964_15545.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1964_15545.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1964_15545.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1964_15545.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15546;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1964_15545.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1964_15545.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1964_15545.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1964_15545.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1964_15545.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1964_15545.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1964_15545.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1964_15545.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1964_15545.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___1964_15548 = env  in
             let uu____15549 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1964_15548.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1964_15548.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1964_15548.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1964_15548.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1964_15548.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1964_15548.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1964_15548.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1964_15548.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1964_15548.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1964_15548.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1964_15548.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1964_15548.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1964_15548.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1964_15548.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1964_15548.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1964_15548.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1964_15548.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1964_15548.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1964_15548.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1964_15548.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1964_15548.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1964_15548.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1964_15548.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1964_15548.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1964_15548.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1964_15548.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1964_15548.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1964_15548.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1964_15548.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1964_15548.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1964_15548.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1964_15548.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1964_15548.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1964_15548.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15549;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1964_15548.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1964_15548.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1964_15548.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1964_15548.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1964_15548.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1964_15548.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1964_15548.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1964_15548.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1964_15548.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____15550) ->
           let env1 =
             let uu___1964_15553 = env  in
             let uu____15554 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1964_15553.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1964_15553.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1964_15553.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1964_15553.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1964_15553.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1964_15553.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1964_15553.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1964_15553.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1964_15553.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1964_15553.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1964_15553.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1964_15553.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1964_15553.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1964_15553.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1964_15553.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1964_15553.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1964_15553.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1964_15553.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1964_15553.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1964_15553.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1964_15553.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1964_15553.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1964_15553.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1964_15553.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1964_15553.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1964_15553.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1964_15553.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1964_15553.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1964_15553.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1964_15553.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1964_15553.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1964_15553.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1964_15553.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1964_15553.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15554;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1964_15553.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1964_15553.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1964_15553.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1964_15553.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1964_15553.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1964_15553.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1964_15553.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1964_15553.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1964_15553.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____15555) ->
           let env1 =
             let uu___1964_15560 = env  in
             let uu____15561 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1964_15560.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1964_15560.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1964_15560.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1964_15560.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1964_15560.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1964_15560.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1964_15560.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1964_15560.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1964_15560.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1964_15560.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1964_15560.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1964_15560.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1964_15560.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1964_15560.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1964_15560.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1964_15560.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1964_15560.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1964_15560.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1964_15560.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1964_15560.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1964_15560.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1964_15560.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1964_15560.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1964_15560.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___1964_15560.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1964_15560.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1964_15560.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1964_15560.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1964_15560.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1964_15560.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1964_15560.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1964_15560.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1964_15560.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1964_15560.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____15561;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1964_15560.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1964_15560.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1964_15560.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1964_15560.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1964_15560.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1964_15560.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1964_15560.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1964_15560.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___1964_15560.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____15563 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15564 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____15574 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____15574) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____15575,uu____15576,uu____15577) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_15582  ->
                   match uu___5_15582 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____15585 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____15587,uu____15588) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_15597  ->
                   match uu___5_15597 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____15600 -> false))
           -> env
       | uu____15602 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____15671 se =
        match uu____15671 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____15724 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____15724
              then
                let uu____15727 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____15727
              else ());
             (let uu____15732 = tc_decl env1 se  in
              match uu____15732 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15785 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15785
                             then
                               let uu____15789 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____15789
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____15805 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____15805
                             then
                               let uu____15809 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____15809
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
                    (let uu____15826 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____15826
                     then
                       let uu____15831 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____15840 =
                                  let uu____15842 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____15842 "\n"  in
                                Prims.op_Hat s uu____15840) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____15831
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____15852 =
                       let uu____15861 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____15861
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____15903 se1 =
                            match uu____15903 with
                            | (exports1,hidden1) ->
                                let uu____15931 = for_export env3 hidden1 se1
                                   in
                                (match uu____15931 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____15852 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____16085 = acc  in
        match uu____16085 with
        | (uu____16120,uu____16121,env1,uu____16123) ->
            let uu____16136 =
              FStar_Util.record_time
                (fun uu____16183  -> process_one_decl acc se)
               in
            (match uu____16136 with
             | (r,ms_elapsed) ->
                 ((let uu____16249 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____16249
                   then
                     let uu____16253 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____16255 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____16253 uu____16255
                   else ());
                  r))
         in
      let uu____16260 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____16260 with
      | (ses1,exports,env1,uu____16308) ->
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
          let uu___2061_16346 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2061_16346.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2061_16346.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2061_16346.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2061_16346.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2061_16346.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2061_16346.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2061_16346.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2061_16346.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2061_16346.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2061_16346.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2061_16346.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2061_16346.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2061_16346.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2061_16346.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2061_16346.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2061_16346.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2061_16346.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2061_16346.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2061_16346.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2061_16346.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2061_16346.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2061_16346.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2061_16346.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2061_16346.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2061_16346.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2061_16346.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2061_16346.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2061_16346.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2061_16346.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2061_16346.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2061_16346.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2061_16346.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2061_16346.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2061_16346.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2061_16346.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2061_16346.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2061_16346.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2061_16346.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2061_16346.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2061_16346.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2061_16346.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____16366 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____16366 with
          | (univs2,t1) ->
              ((let uu____16374 =
                  let uu____16376 =
                    let uu____16382 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____16382  in
                  FStar_All.pipe_left uu____16376
                    (FStar_Options.Other "Exports")
                   in
                if uu____16374
                then
                  let uu____16386 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____16388 =
                    let uu____16390 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____16390
                      (FStar_String.concat ", ")
                     in
                  let uu____16407 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____16386 uu____16388 uu____16407
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____16413 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____16413 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____16439 =
             let uu____16441 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____16443 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____16441 uu____16443
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____16439);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16454) ->
              let uu____16463 =
                let uu____16465 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16465  in
              if uu____16463
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____16479,uu____16480) ->
              let t =
                let uu____16492 =
                  let uu____16499 =
                    let uu____16500 =
                      let uu____16515 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____16515)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____16500  in
                  FStar_Syntax_Syntax.mk uu____16499  in
                uu____16492 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____16531,uu____16532,uu____16533) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____16543 =
                let uu____16545 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16545  in
              if uu____16543 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____16553,lbs),uu____16555) ->
              let uu____16566 =
                let uu____16568 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16568  in
              if uu____16566
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
              let uu____16591 =
                let uu____16593 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____16593  in
              if uu____16591
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____16614 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____16615 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____16622 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16623 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____16624 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____16625 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____16632 -> ()  in
        let uu____16633 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____16633 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____16739) -> true
             | uu____16741 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____16771 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____16810 ->
                   let uu____16811 =
                     let uu____16818 =
                       let uu____16819 =
                         let uu____16834 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____16834)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____16819  in
                     FStar_Syntax_Syntax.mk uu____16818  in
                   uu____16811 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____16851,uu____16852) ->
            let s1 =
              let uu___2187_16862 = s  in
              let uu____16863 =
                let uu____16864 =
                  let uu____16871 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____16871)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____16864  in
              let uu____16872 =
                let uu____16875 =
                  let uu____16878 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____16878  in
                FStar_Syntax_Syntax.Assumption :: uu____16875  in
              {
                FStar_Syntax_Syntax.sigel = uu____16863;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2187_16862.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____16872;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2187_16862.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2187_16862.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____16881 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____16906 lbdef =
        match uu____16906 with
        | (uvs,t) ->
            let attrs =
              let uu____16917 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____16917
              then
                let uu____16922 =
                  let uu____16923 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____16923
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____16922 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2200_16926 = s  in
            let uu____16927 =
              let uu____16930 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____16930  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2200_16926.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____16927;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2200_16926.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____16948 -> failwith "Impossible!"  in
        let c_opt =
          let uu____16955 = FStar_Syntax_Util.is_unit t  in
          if uu____16955
          then
            let uu____16962 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____16962
          else
            (let uu____16969 =
               let uu____16970 = FStar_Syntax_Subst.compress t  in
               uu____16970.FStar_Syntax_Syntax.n  in
             match uu____16969 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____16977,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____17001 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____17013 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____17013
            then false
            else
              (let uu____17020 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____17020
               then true
               else
                 (let uu____17027 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____17027))
         in
      let extract_sigelt s =
        (let uu____17039 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____17039
         then
           let uu____17042 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____17042
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____17049 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____17069 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____17088 ->
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
                             (lid,uu____17134,uu____17135,uu____17136,uu____17137,uu____17138)
                             ->
                             ((let uu____17148 =
                                 let uu____17151 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____17151  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____17148);
                              (let uu____17200 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____17200 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____17204,uu____17205,uu____17206,uu____17207,uu____17208)
                             ->
                             ((let uu____17216 =
                                 let uu____17219 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____17219  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____17216);
                              sigelts1)
                         | uu____17268 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____17277 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____17277
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____17287 =
                    let uu___2264_17288 = s  in
                    let uu____17289 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2264_17288.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2264_17288.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____17289;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2264_17288.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2264_17288.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____17287])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____17300 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____17300
             then []
             else
               (let uu____17307 = lbs  in
                match uu____17307 with
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
                        (fun uu____17369  ->
                           match uu____17369 with
                           | (uu____17377,t,uu____17379) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____17396  ->
                             match uu____17396 with
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
                           (fun uu____17423  ->
                              match uu____17423 with
                              | (uu____17431,t,uu____17433) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____17445,uu____17446) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____17454 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____17483 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____17483) uu____17454
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____17487 =
                    let uu___2306_17488 = s  in
                    let uu____17489 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2306_17488.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2306_17488.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____17489;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2306_17488.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2306_17488.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____17487]
                else [])
             else
               (let uu____17496 =
                  let uu___2308_17497 = s  in
                  let uu____17498 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2308_17497.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2308_17497.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____17498;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2308_17497.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2308_17497.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____17496])
         | FStar_Syntax_Syntax.Sig_new_effect uu____17501 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____17502 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____17503 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____17504 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____17517 -> [s])
         in
      let uu___2320_17518 = m  in
      let uu____17519 =
        let uu____17520 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____17520 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2320_17518.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____17519;
        FStar_Syntax_Syntax.exports =
          (uu___2320_17518.FStar_Syntax_Syntax.exports);
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
        (fun uu____17571  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____17618  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____17633 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____17633
  
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
      (let uu____17722 = FStar_Options.debug_any ()  in
       if uu____17722
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
         let uu___2345_17738 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2345_17738.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2345_17738.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2345_17738.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2345_17738.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2345_17738.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2345_17738.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2345_17738.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2345_17738.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2345_17738.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2345_17738.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2345_17738.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2345_17738.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2345_17738.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2345_17738.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2345_17738.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2345_17738.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2345_17738.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2345_17738.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2345_17738.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2345_17738.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2345_17738.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2345_17738.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2345_17738.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2345_17738.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2345_17738.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2345_17738.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2345_17738.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2345_17738.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2345_17738.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2345_17738.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2345_17738.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2345_17738.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2345_17738.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2345_17738.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2345_17738.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2345_17738.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2345_17738.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2345_17738.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2345_17738.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2345_17738.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2345_17738.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2345_17738.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____17740 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____17740 with
       | (ses,exports,env3) ->
           ((let uu___2353_17773 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2353_17773.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2353_17773.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2353_17773.FStar_Syntax_Syntax.is_interface)
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
        let uu____17802 = tc_decls env decls  in
        match uu____17802 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2362_17833 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2362_17833.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2362_17833.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2362_17833.FStar_Syntax_Syntax.is_interface)
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
        let uu____17894 = tc_partial_modul env01 m  in
        match uu____17894 with
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
                (let uu____17931 = FStar_Errors.get_err_count ()  in
                 uu____17931 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____17942 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____17942
                then
                  let uu____17946 =
                    let uu____17948 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17948 then "" else " (in lax mode) "  in
                  let uu____17956 =
                    let uu____17958 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17958
                    then
                      let uu____17962 =
                        let uu____17964 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____17964 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____17962
                    else ""  in
                  let uu____17971 =
                    let uu____17973 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____17973
                    then
                      let uu____17977 =
                        let uu____17979 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____17979 "\n"  in
                      Prims.op_Hat "\nto: " uu____17977
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____17946
                    uu____17956 uu____17971
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2388_17993 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2388_17993.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2388_17993.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2388_17993.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2388_17993.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2388_17993.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2388_17993.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2388_17993.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2388_17993.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2388_17993.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2388_17993.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2388_17993.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2388_17993.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2388_17993.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2388_17993.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2388_17993.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2388_17993.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2388_17993.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2388_17993.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2388_17993.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2388_17993.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2388_17993.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2388_17993.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2388_17993.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2388_17993.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2388_17993.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2388_17993.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2388_17993.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2388_17993.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2388_17993.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2388_17993.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2388_17993.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2388_17993.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2388_17993.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2388_17993.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2388_17993.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2388_17993.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2388_17993.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2388_17993.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2388_17993.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2388_17993.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2388_17993.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2388_17993.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2388_17993.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2391_17995 = en01  in
                    let uu____17996 =
                      let uu____18011 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____18011, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2391_17995.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2391_17995.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2391_17995.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2391_17995.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2391_17995.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2391_17995.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2391_17995.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2391_17995.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2391_17995.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2391_17995.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2391_17995.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2391_17995.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2391_17995.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2391_17995.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2391_17995.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2391_17995.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2391_17995.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2391_17995.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2391_17995.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2391_17995.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2391_17995.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2391_17995.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2391_17995.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2391_17995.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2391_17995.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2391_17995.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2391_17995.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2391_17995.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2391_17995.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2391_17995.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2391_17995.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____17996;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2391_17995.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2391_17995.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2391_17995.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2391_17995.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2391_17995.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2391_17995.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2391_17995.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2391_17995.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2391_17995.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2391_17995.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2391_17995.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2391_17995.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____18057 =
                    let uu____18059 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____18059  in
                  if uu____18057
                  then
                    ((let uu____18063 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____18063 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____18067 = tc_modul en0 modul_iface true  in
                match uu____18067 with
                | (modul_iface1,env) ->
                    ((let uu___2400_18080 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2400_18080.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2400_18080.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2400_18080.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2402_18084 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2402_18084.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2402_18084.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2402_18084.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____18087 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____18087 FStar_Util.smap_clear);
               (let uu____18123 =
                  ((let uu____18127 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____18127) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____18130 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____18130)
                   in
                if uu____18123 then check_exports env modul exports else ());
               (let uu____18136 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____18136 (fun a4  -> ()));
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
        let uu____18151 =
          let uu____18153 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____18153  in
        push_context env uu____18151  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____18174 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____18185 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____18185 with | (uu____18192,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____18217 = FStar_Options.debug_any ()  in
         if uu____18217
         then
           let uu____18220 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____18220
         else ());
        (let uu____18232 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____18232
         then
           let uu____18235 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____18235
         else ());
        (let env1 =
           let uu___2432_18241 = env  in
           let uu____18242 =
             let uu____18244 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____18244  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2432_18241.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2432_18241.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2432_18241.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2432_18241.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2432_18241.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2432_18241.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2432_18241.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2432_18241.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2432_18241.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2432_18241.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2432_18241.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2432_18241.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2432_18241.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2432_18241.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2432_18241.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2432_18241.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2432_18241.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2432_18241.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2432_18241.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2432_18241.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____18242;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2432_18241.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2432_18241.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2432_18241.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2432_18241.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2432_18241.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2432_18241.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2432_18241.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2432_18241.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2432_18241.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2432_18241.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2432_18241.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2432_18241.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2432_18241.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2432_18241.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2432_18241.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2432_18241.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2432_18241.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2432_18241.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2432_18241.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2432_18241.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2432_18241.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2432_18241.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2432_18241.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____18246 = tc_modul env1 m b  in
         match uu____18246 with
         | (m1,env2) ->
             ((let uu____18258 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____18258
               then
                 let uu____18261 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____18261
               else ());
              (let uu____18267 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____18267
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
                         let uu____18305 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____18305 with
                         | (univnames1,e) ->
                             let uu___2454_18312 = lb  in
                             let uu____18313 =
                               let uu____18316 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____18316 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2454_18312.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2454_18312.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2454_18312.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2454_18312.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____18313;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2454_18312.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2454_18312.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2456_18317 = se  in
                       let uu____18318 =
                         let uu____18319 =
                           let uu____18326 =
                             let uu____18327 = FStar_List.map update lbs  in
                             (b1, uu____18327)  in
                           (uu____18326, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____18319  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____18318;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2456_18317.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2456_18317.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2456_18317.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2456_18317.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____18335 -> se  in
                 let normalized_module =
                   let uu___2460_18337 = m1  in
                   let uu____18338 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2460_18337.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____18338;
                     FStar_Syntax_Syntax.exports =
                       (uu___2460_18337.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2460_18337.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____18339 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____18339
               else ());
              (m1, env2)))
  