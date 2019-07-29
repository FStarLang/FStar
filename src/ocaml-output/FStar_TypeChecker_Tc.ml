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
                                      let uu____1546 =
                                        let uu____1551 =
                                          let uu____1552 =
                                            FStar_Syntax_Subst.close_univ_vars
                                              annotated_univ_names repr
                                             in
                                          (annotated_univ_names, uu____1552)
                                           in
                                        FStar_TypeChecker_Env.inst_tscheme
                                          uu____1551
                                         in
                                      (match uu____1546 with
                                       | (uu____1563,repr1) ->
                                           let uu____1565 =
                                             get_binders_from_signature
                                               signature1
                                              in
                                           (uu____1565, repr1)))
                              in
                           (match uu____1494 with
                            | (b_bs,b_repr) ->
                                let b_bs1 =
                                  FStar_Syntax_Subst.open_binders b_bs  in
                                let uu____1573 =
                                  let uu____1592 = FStar_List.hd b_bs1  in
                                  let uu____1605 = FStar_List.tl b_bs1  in
                                  (uu____1592, uu____1605)  in
                                (match uu____1573 with
                                 | (b,b_bs_indices) ->
                                     let b_bs_indices_arrow =
                                       FStar_All.pipe_right b_bs_indices
                                         (FStar_List.map
                                            (fun uu____1709  ->
                                               match uu____1709 with
                                               | (b1,q) ->
                                                   let uu____1728 =
                                                     let uu___216_1729 = b1
                                                        in
                                                     let uu____1730 =
                                                       let uu____1733 =
                                                         let uu____1742 =
                                                           let uu____1749 =
                                                             let uu____1750 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____1750
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____1749
                                                            in
                                                         [uu____1742]  in
                                                       let uu____1771 =
                                                         FStar_Syntax_Syntax.mk_Total
                                                           b1.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         uu____1733
                                                         uu____1771
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.ppname
                                                         =
                                                         (uu___216_1729.FStar_Syntax_Syntax.ppname);
                                                       FStar_Syntax_Syntax.index
                                                         =
                                                         (uu___216_1729.FStar_Syntax_Syntax.index);
                                                       FStar_Syntax_Syntax.sort
                                                         = uu____1730
                                                     }  in
                                                   (uu____1728, q)))
                                        in
                                     let f_b =
                                       let uu____1777 =
                                         let uu____1778 =
                                           let uu____1783 =
                                             let uu____1784 =
                                               let uu____1787 =
                                                 FStar_All.pipe_right (a ::
                                                   bs_indices)
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____1787
                                                 (FStar_List.map
                                                    FStar_Syntax_Syntax.bv_to_name)
                                                in
                                             FStar_All.pipe_right uu____1784
                                               (FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg)
                                              in
                                           FStar_Syntax_Syntax.mk_Tm_app repr
                                             uu____1783
                                            in
                                         uu____1778
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                          in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____1777
                                        in
                                     let g_b =
                                       let b_arg =
                                         let uu____1830 =
                                           let uu____1831 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____1831
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_All.pipe_right uu____1830
                                           FStar_Syntax_Syntax.as_arg
                                          in
                                       let x =
                                         let uu____1849 =
                                           let uu____1850 =
                                             FStar_All.pipe_right a
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____1850
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_Syntax_Syntax.null_binder
                                           uu____1849
                                          in
                                       let b_indices_args =
                                         let uu____1870 =
                                           let uu____1873 =
                                             FStar_All.pipe_right
                                               b_bs_indices_arrow
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst)
                                              in
                                           FStar_All.pipe_right uu____1873
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.bv_to_name)
                                            in
                                         FStar_All.pipe_right uu____1870
                                           (FStar_List.map
                                              (fun t  ->
                                                 let uu____1913 =
                                                   let uu____1914 =
                                                     let uu____1919 =
                                                       let uu____1920 =
                                                         let uu____1929 =
                                                           let uu____1930 =
                                                             FStar_All.pipe_right
                                                               x
                                                               FStar_Pervasives_Native.fst
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____1930
                                                             FStar_Syntax_Syntax.bv_to_name
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____1929
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____1920]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       t uu____1919
                                                      in
                                                   uu____1914
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1913
                                                   FStar_Syntax_Syntax.as_arg))
                                          in
                                       let repr_app =
                                         FStar_Syntax_Syntax.mk_Tm_app b_repr
                                           (b_arg :: b_indices_args)
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                          in
                                       let uu____1974 =
                                         let uu____1975 =
                                           FStar_Syntax_Syntax.mk_Total
                                             repr_app
                                            in
                                         FStar_Syntax_Util.arrow [x]
                                           uu____1975
                                          in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____1974
                                        in
                                     let bs2 = a :: b ::
                                       (FStar_List.append bs_indices
                                          (FStar_List.append
                                             b_bs_indices_arrow [f_b; g_b]))
                                        in
                                     let uu____2041 =
                                       let env1 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs2
                                          in
                                       FStar_List.fold_left
                                         (fun uu____2085  ->
                                            fun uu____2086  ->
                                              match (uu____2085, uu____2086)
                                              with
                                              | ((uvars1,gs,bs_substs),
                                                 (b1,uu____2139)) ->
                                                  let uu____2174 =
                                                    let uu____2187 =
                                                      FStar_Syntax_Subst.subst
                                                        bs_substs
                                                        b1.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      "" r env1 uu____2187
                                                     in
                                                  (match uu____2174 with
                                                   | (t,uu____2202,g) ->
                                                       let uu____2216 =
                                                         let uu____2219 =
                                                           let uu____2222 =
                                                             FStar_All.pipe_right
                                                               t
                                                               FStar_Syntax_Syntax.as_arg
                                                              in
                                                           [uu____2222]  in
                                                         FStar_List.append
                                                           uvars1 uu____2219
                                                          in
                                                       (uu____2216,
                                                         (FStar_List.append
                                                            gs [g]),
                                                         (FStar_List.append
                                                            bs_substs
                                                            [FStar_Syntax_Syntax.NT
                                                               (b1, t)]))))
                                         ([], [], []) b_bs_indices
                                        in
                                     (match uu____2041 with
                                      | (uvars1,gs,uu____2243) ->
                                          let expected_bind_repr_type =
                                            let repr_args =
                                              let uu____2262 =
                                                FStar_Syntax_Util.arg_of_non_null_binder
                                                  b
                                                 in
                                              uu____2262 :: uvars1  in
                                            let repr_comp =
                                              let uu____2266 =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  b_repr repr_args
                                                  FStar_Pervasives_Native.None
                                                  r
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____2266
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
                                          ((let uu____2270 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffects")
                                               in
                                            if uu____2270
                                            then
                                              let uu____2275 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  ed2.FStar_Syntax_Syntax.bind_repr
                                                 in
                                              let uu____2277 =
                                                FStar_Syntax_Print.term_to_string
                                                  expected_bind_repr_type
                                                 in
                                              FStar_Util.print2
                                                "Checking bind_repr: %s against expected bind_repr type: %s\n"
                                                uu____2275 uu____2277
                                            else ());
                                           (let bind_repr =
                                              check_and_gen1
                                                (let uu___250_2293 = env  in
                                                 {
                                                   FStar_TypeChecker_Env.solver
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.solver);
                                                   FStar_TypeChecker_Env.range
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.range);
                                                   FStar_TypeChecker_Env.curmodule
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.curmodule);
                                                   FStar_TypeChecker_Env.gamma
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.gamma);
                                                   FStar_TypeChecker_Env.gamma_sig
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.gamma_sig);
                                                   FStar_TypeChecker_Env.gamma_cache
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.gamma_cache);
                                                   FStar_TypeChecker_Env.modules
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.modules);
                                                   FStar_TypeChecker_Env.expected_typ
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.expected_typ);
                                                   FStar_TypeChecker_Env.sigtab
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.sigtab);
                                                   FStar_TypeChecker_Env.attrtab
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.attrtab);
                                                   FStar_TypeChecker_Env.is_pattern
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.is_pattern);
                                                   FStar_TypeChecker_Env.instantiate_imp
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.instantiate_imp);
                                                   FStar_TypeChecker_Env.effects
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.effects);
                                                   FStar_TypeChecker_Env.generalize
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.generalize);
                                                   FStar_TypeChecker_Env.letrecs
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.letrecs);
                                                   FStar_TypeChecker_Env.top_level
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.top_level);
                                                   FStar_TypeChecker_Env.check_uvars
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.check_uvars);
                                                   FStar_TypeChecker_Env.use_eq
                                                     = true;
                                                   FStar_TypeChecker_Env.is_iface
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.is_iface);
                                                   FStar_TypeChecker_Env.admit
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.admit);
                                                   FStar_TypeChecker_Env.lax
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.lax);
                                                   FStar_TypeChecker_Env.lax_universes
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.lax_universes);
                                                   FStar_TypeChecker_Env.phase1
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.phase1);
                                                   FStar_TypeChecker_Env.failhard
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.failhard);
                                                   FStar_TypeChecker_Env.nosynth
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.nosynth);
                                                   FStar_TypeChecker_Env.uvar_subtyping
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.uvar_subtyping);
                                                   FStar_TypeChecker_Env.tc_term
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.tc_term);
                                                   FStar_TypeChecker_Env.type_of
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.type_of);
                                                   FStar_TypeChecker_Env.universe_of
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.universe_of);
                                                   FStar_TypeChecker_Env.check_type_of
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.check_type_of);
                                                   FStar_TypeChecker_Env.use_bv_sorts
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.use_bv_sorts);
                                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                   FStar_TypeChecker_Env.normalized_eff_names
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.normalized_eff_names);
                                                   FStar_TypeChecker_Env.fv_delta_depths
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.fv_delta_depths);
                                                   FStar_TypeChecker_Env.proof_ns
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.proof_ns);
                                                   FStar_TypeChecker_Env.synth_hook
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.synth_hook);
                                                   FStar_TypeChecker_Env.splice
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.splice);
                                                   FStar_TypeChecker_Env.postprocess
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.postprocess);
                                                   FStar_TypeChecker_Env.is_native_tactic
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.is_native_tactic);
                                                   FStar_TypeChecker_Env.identifier_info
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.identifier_info);
                                                   FStar_TypeChecker_Env.tc_hooks
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.tc_hooks);
                                                   FStar_TypeChecker_Env.dsenv
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.dsenv);
                                                   FStar_TypeChecker_Env.nbe
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.nbe);
                                                   FStar_TypeChecker_Env.strict_args_tab
                                                     =
                                                     (uu___250_2293.FStar_TypeChecker_Env.strict_args_tab)
                                                 })
                                                ed2.FStar_Syntax_Syntax.bind_repr
                                                expected_bind_repr_type
                                               in
                                            FStar_List.iter
                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                 env) gs;
                                            (let uu____2297 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2297
                                             then
                                               let uu____2302 =
                                                 FStar_Syntax_Print.tscheme_to_string
                                                   bind_repr
                                                  in
                                               let uu____2304 =
                                                 FStar_Syntax_Print.term_to_string
                                                   expected_bind_repr_type
                                                  in
                                               FStar_Util.print2
                                                 "Checked bind_repr: %s against expected bind_repr type: %s\n"
                                                 uu____2302 uu____2304
                                             else ());
                                            (let bs3 = a :: b ::
                                               (FStar_List.append bs_indices
                                                  b_bs_indices_arrow)
                                                in
                                             let indices =
                                               let uu____2339 =
                                                 FStar_All.pipe_right uvars1
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2339
                                                 (FStar_List.map
                                                    FStar_Syntax_Subst.compress)
                                                in
                                             let embedded_indices =
                                               let uu____2365 =
                                                 let uu____2372 =
                                                   FStar_Syntax_Embeddings.e_list
                                                     FStar_Syntax_Embeddings.e_any
                                                    in
                                                 FStar_Syntax_Embeddings.embed
                                                   uu____2372 indices
                                                  in
                                               uu____2365
                                                 FStar_Range.dummyRange
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Embeddings.id_norm_cb
                                                in
                                             let bind_wp =
                                               let uu____2382 =
                                                 let uu____2383 =
                                                   FStar_Syntax_Subst.close_binders
                                                     bs3
                                                    in
                                                 let uu____2384 =
                                                   FStar_Syntax_Subst.close
                                                     bs3 embedded_indices
                                                    in
                                                 FStar_Syntax_Util.abs
                                                   uu____2383 uu____2384
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2382
                                                 (FStar_TypeChecker_Util.generalize_universes
                                                    env)
                                                in
                                             (let uu____2388 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____2388
                                              then
                                                let uu____2393 =
                                                  FStar_Syntax_Print.tscheme_to_string
                                                    bind_wp
                                                   in
                                                FStar_Util.print1
                                                  "bind_wp: %s\n" uu____2393
                                              else ());
                                             (bind_repr, bind_wp)))))))
                        in
                     (match uu____1392 with
                      | (bind_repr,bind_wp) ->
                          let tc_action env01 act =
                            if
                              (FStar_List.length
                                 act.FStar_Syntax_Syntax.action_params)
                                <> Prims.int_zero
                            then
                              failwith
                                (Prims.op_Hat
                                   "tc_layered_eff_decl: action_params are not empty for "
                                   (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str)
                            else ();
                            (let uu____2424 =
                               match act.FStar_Syntax_Syntax.action_univs
                               with
                               | [] -> ([], [], act, env01)
                               | us ->
                                   let uu____2454 =
                                     FStar_Syntax_Subst.univ_var_opening us
                                      in
                                   (match uu____2454 with
                                    | (univ_subst,univs1) ->
                                        let uu____2485 =
                                          let uu___275_2486 = act  in
                                          let uu____2487 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst
                                              act.FStar_Syntax_Syntax.action_defn
                                             in
                                          let uu____2488 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst
                                              act.FStar_Syntax_Syntax.action_typ
                                             in
                                          {
                                            FStar_Syntax_Syntax.action_name =
                                              (uu___275_2486.FStar_Syntax_Syntax.action_name);
                                            FStar_Syntax_Syntax.action_unqualified_name
                                              =
                                              (uu___275_2486.FStar_Syntax_Syntax.action_unqualified_name);
                                            FStar_Syntax_Syntax.action_univs
                                              = univs1;
                                            FStar_Syntax_Syntax.action_params
                                              =
                                              (uu___275_2486.FStar_Syntax_Syntax.action_params);
                                            FStar_Syntax_Syntax.action_defn =
                                              uu____2487;
                                            FStar_Syntax_Syntax.action_typ =
                                              uu____2488
                                          }  in
                                        let uu____2489 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env01 univs1
                                           in
                                        (univs1, univ_subst, uu____2485,
                                          uu____2489))
                                in
                             match uu____2424 with
                             | (univs1,univ_subst,act1,env1) ->
                                 let act_typ =
                                   let uu____2507 =
                                     let uu____2508 =
                                       FStar_Syntax_Subst.compress
                                         act1.FStar_Syntax_Syntax.action_typ
                                        in
                                     uu____2508.FStar_Syntax_Syntax.n  in
                                   match uu____2507 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs1,c) ->
                                       let ct =
                                         FStar_Syntax_Util.comp_to_comp_typ c
                                          in
                                       let uu____2534 =
                                         FStar_Ident.lid_equals
                                           ct.FStar_Syntax_Syntax.effect_name
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       if uu____2534
                                       then
                                         let c1 =
                                           let uu____2540 =
                                             let uu____2541 =
                                               FStar_All.pipe_right repr
                                                 (FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.EraseUniverses;
                                                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                    env1)
                                                in
                                             FStar_All.pipe_right uu____2541
                                               (fun repr1  ->
                                                  let uu____2547 =
                                                    let uu____2552 =
                                                      let uu____2553 =
                                                        FStar_All.pipe_right
                                                          ct.FStar_Syntax_Syntax.result_typ
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      uu____2553 ::
                                                        (ct.FStar_Syntax_Syntax.effect_args)
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      repr1 uu____2552
                                                     in
                                                  uu____2547
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange)
                                              in
                                           FStar_All.pipe_right uu____2540
                                             FStar_Syntax_Syntax.mk_Total
                                            in
                                         FStar_Syntax_Util.arrow bs1 c1
                                       else
                                         act1.FStar_Syntax_Syntax.action_typ
                                   | uu____2582 ->
                                       act1.FStar_Syntax_Syntax.action_typ
                                    in
                                 let uu____2583 =
                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                     env1 act_typ
                                    in
                                 (match uu____2583 with
                                  | (act_typ1,uu____2591,g_t) ->
                                      let uu____2593 =
                                        let uu____2600 =
                                          let uu___296_2601 =
                                            FStar_TypeChecker_Env.set_expected_typ
                                              env1 act_typ1
                                             in
                                          {
                                            FStar_TypeChecker_Env.solver =
                                              (uu___296_2601.FStar_TypeChecker_Env.solver);
                                            FStar_TypeChecker_Env.range =
                                              (uu___296_2601.FStar_TypeChecker_Env.range);
                                            FStar_TypeChecker_Env.curmodule =
                                              (uu___296_2601.FStar_TypeChecker_Env.curmodule);
                                            FStar_TypeChecker_Env.gamma =
                                              (uu___296_2601.FStar_TypeChecker_Env.gamma);
                                            FStar_TypeChecker_Env.gamma_sig =
                                              (uu___296_2601.FStar_TypeChecker_Env.gamma_sig);
                                            FStar_TypeChecker_Env.gamma_cache
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.gamma_cache);
                                            FStar_TypeChecker_Env.modules =
                                              (uu___296_2601.FStar_TypeChecker_Env.modules);
                                            FStar_TypeChecker_Env.expected_typ
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.expected_typ);
                                            FStar_TypeChecker_Env.sigtab =
                                              (uu___296_2601.FStar_TypeChecker_Env.sigtab);
                                            FStar_TypeChecker_Env.attrtab =
                                              (uu___296_2601.FStar_TypeChecker_Env.attrtab);
                                            FStar_TypeChecker_Env.is_pattern
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.is_pattern);
                                            FStar_TypeChecker_Env.instantiate_imp
                                              = false;
                                            FStar_TypeChecker_Env.effects =
                                              (uu___296_2601.FStar_TypeChecker_Env.effects);
                                            FStar_TypeChecker_Env.generalize
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.generalize);
                                            FStar_TypeChecker_Env.letrecs =
                                              (uu___296_2601.FStar_TypeChecker_Env.letrecs);
                                            FStar_TypeChecker_Env.top_level =
                                              (uu___296_2601.FStar_TypeChecker_Env.top_level);
                                            FStar_TypeChecker_Env.check_uvars
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.check_uvars);
                                            FStar_TypeChecker_Env.use_eq =
                                              (uu___296_2601.FStar_TypeChecker_Env.use_eq);
                                            FStar_TypeChecker_Env.is_iface =
                                              (uu___296_2601.FStar_TypeChecker_Env.is_iface);
                                            FStar_TypeChecker_Env.admit =
                                              (uu___296_2601.FStar_TypeChecker_Env.admit);
                                            FStar_TypeChecker_Env.lax =
                                              (uu___296_2601.FStar_TypeChecker_Env.lax);
                                            FStar_TypeChecker_Env.lax_universes
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.lax_universes);
                                            FStar_TypeChecker_Env.phase1 =
                                              (uu___296_2601.FStar_TypeChecker_Env.phase1);
                                            FStar_TypeChecker_Env.failhard =
                                              (uu___296_2601.FStar_TypeChecker_Env.failhard);
                                            FStar_TypeChecker_Env.nosynth =
                                              (uu___296_2601.FStar_TypeChecker_Env.nosynth);
                                            FStar_TypeChecker_Env.uvar_subtyping
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.uvar_subtyping);
                                            FStar_TypeChecker_Env.tc_term =
                                              (uu___296_2601.FStar_TypeChecker_Env.tc_term);
                                            FStar_TypeChecker_Env.type_of =
                                              (uu___296_2601.FStar_TypeChecker_Env.type_of);
                                            FStar_TypeChecker_Env.universe_of
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.universe_of);
                                            FStar_TypeChecker_Env.check_type_of
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.check_type_of);
                                            FStar_TypeChecker_Env.use_bv_sorts
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.use_bv_sorts);
                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.qtbl_name_and_index);
                                            FStar_TypeChecker_Env.normalized_eff_names
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.normalized_eff_names);
                                            FStar_TypeChecker_Env.fv_delta_depths
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.fv_delta_depths);
                                            FStar_TypeChecker_Env.proof_ns =
                                              (uu___296_2601.FStar_TypeChecker_Env.proof_ns);
                                            FStar_TypeChecker_Env.synth_hook
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.synth_hook);
                                            FStar_TypeChecker_Env.splice =
                                              (uu___296_2601.FStar_TypeChecker_Env.splice);
                                            FStar_TypeChecker_Env.postprocess
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.postprocess);
                                            FStar_TypeChecker_Env.is_native_tactic
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.is_native_tactic);
                                            FStar_TypeChecker_Env.identifier_info
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.identifier_info);
                                            FStar_TypeChecker_Env.tc_hooks =
                                              (uu___296_2601.FStar_TypeChecker_Env.tc_hooks);
                                            FStar_TypeChecker_Env.dsenv =
                                              (uu___296_2601.FStar_TypeChecker_Env.dsenv);
                                            FStar_TypeChecker_Env.nbe =
                                              (uu___296_2601.FStar_TypeChecker_Env.nbe);
                                            FStar_TypeChecker_Env.strict_args_tab
                                              =
                                              (uu___296_2601.FStar_TypeChecker_Env.strict_args_tab)
                                          }  in
                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                          uu____2600
                                          act1.FStar_Syntax_Syntax.action_defn
                                         in
                                      (match uu____2593 with
                                       | (act_defn,uu____2604,g_a) ->
                                           let act_typ2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 act_typ1
                                              in
                                           let uu____2607 =
                                             let uu____2618 =
                                               match annotated_univ_names
                                               with
                                               | [] ->
                                                   let uu____2627 =
                                                     FStar_TypeChecker_TcTerm.tc_trivial_guard
                                                       env1 signature0
                                                      in
                                                   (match uu____2627 with
                                                    | (signature1,uu____2637)
                                                        ->
                                                        let b_bs =
                                                          get_binders_from_signature
                                                            signature1
                                                           in
                                                        let repr1 =
                                                          tc_repr repr0 b_bs
                                                           in
                                                        (b_bs, repr1))
                                               | uu____2648 ->
                                                   let uu____2651 =
                                                     let uu____2656 =
                                                       let uu____2657 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           annotated_univ_names
                                                           ed2.FStar_Syntax_Syntax.signature
                                                          in
                                                       (annotated_univ_names,
                                                         uu____2657)
                                                        in
                                                     FStar_TypeChecker_Env.inst_tscheme
                                                       uu____2656
                                                      in
                                                   (match uu____2651 with
                                                    | (uu____2668,signature1)
                                                        ->
                                                        let uu____2670 =
                                                          let uu____2675 =
                                                            let uu____2676 =
                                                              FStar_Syntax_Subst.close_univ_vars
                                                                annotated_univ_names
                                                                repr
                                                               in
                                                            (annotated_univ_names,
                                                              uu____2676)
                                                             in
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            uu____2675
                                                           in
                                                        (match uu____2670
                                                         with
                                                         | (uu____2687,repr1)
                                                             ->
                                                             let uu____2689 =
                                                               get_binders_from_signature
                                                                 signature1
                                                                in
                                                             (uu____2689,
                                                               repr1)))
                                                in
                                             match uu____2618 with
                                             | (act_bs,act_repr) ->
                                                 let act_bs1 =
                                                   FStar_Syntax_Subst.open_binders
                                                     act_bs
                                                    in
                                                 let uu____2703 =
                                                   let uu____2708 =
                                                     let uu____2709 =
                                                       FStar_Syntax_Subst.compress
                                                         act_typ2
                                                        in
                                                     uu____2709.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____2708 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (bs1,c) ->
                                                       FStar_Syntax_Subst.open_comp
                                                         bs1 c
                                                   | uu____2738 ->
                                                       failwith
                                                         "tc_layered_eff_decl: actions must have arrow types"
                                                    in
                                                 (match uu____2703 with
                                                  | (act_typ_bs,act_typ_c) ->
                                                      let uu____2756 =
                                                        let env2 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env1 act_typ_bs
                                                           in
                                                        FStar_List.fold_left
                                                          (fun uu____2800  ->
                                                             fun uu____2801 
                                                               ->
                                                               match 
                                                                 (uu____2800,
                                                                   uu____2801)
                                                               with
                                                               | ((uvars1,gs,bs_substs),
                                                                  (b,uu____2854))
                                                                   ->
                                                                   let uu____2889
                                                                    =
                                                                    let uu____2902
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    bs_substs
                                                                    b.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_TypeChecker_Util.new_implicit_var
                                                                    ""
                                                                    FStar_Range.dummyRange
                                                                    env2
                                                                    uu____2902
                                                                     in
                                                                   (match uu____2889
                                                                    with
                                                                    | 
                                                                    (t,uu____2917,g)
                                                                    ->
                                                                    let uu____2931
                                                                    =
                                                                    let uu____2934
                                                                    =
                                                                    let uu____2937
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____2937]
                                                                     in
                                                                    FStar_List.append
                                                                    uvars1
                                                                    uu____2934
                                                                     in
                                                                    (uu____2931,
                                                                    (FStar_List.append
                                                                    gs [g]),
                                                                    (FStar_List.append
                                                                    bs_substs
                                                                    [
                                                                    FStar_Syntax_Syntax.NT
                                                                    (b, t)]))))
                                                          ([], [], [])
                                                          act_bs1
                                                         in
                                                      (match uu____2756 with
                                                       | (uvars1,gs,uu____2964)
                                                           ->
                                                           let repr_comp =
                                                             let uu____2978 =
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 act_repr
                                                                 uvars1
                                                                 FStar_Pervasives_Native.None
                                                                 FStar_Range.dummyRange
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____2978
                                                              in
                                                           let expected_act_typ
                                                             =
                                                             FStar_Syntax_Util.arrow
                                                               act_typ_bs
                                                               repr_comp
                                                              in
                                                           ((let uu____2983 =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffects")
                                                                in
                                                             if uu____2983
                                                             then
                                                               let uu____2988
                                                                 =
                                                                 let uu____2990
                                                                   =
                                                                   FStar_Syntax_Util.arrow
                                                                    act_typ_bs
                                                                    act_typ_c
                                                                    in
                                                                 FStar_Syntax_Print.term_to_string
                                                                   uu____2990
                                                                  in
                                                               let uu____2991
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   expected_act_typ
                                                                  in
                                                               FStar_Util.print2
                                                                 "Trying teq of act_typ: %s and expected_act_typ: %s\n"
                                                                 uu____2988
                                                                 uu____2991
                                                             else ());
                                                            (let g =
                                                               let uu____2997
                                                                 =
                                                                 FStar_Syntax_Util.arrow
                                                                   act_typ_bs
                                                                   act_typ_c
                                                                  in
                                                               FStar_TypeChecker_Rel.teq
                                                                 env1
                                                                 uu____2997
                                                                 expected_act_typ
                                                                in
                                                             (expected_act_typ,
                                                               repr_comp, gs,
                                                               g)))))
                                              in
                                           (match uu____2607 with
                                            | (expected_act_typ,repr_comp,guvars,g)
                                                ->
                                                (FStar_All.pipe_right (g_t ::
                                                   g_a :: g :: guvars)
                                                   (FStar_List.iter
                                                      (FStar_TypeChecker_Rel.force_trivial_guard
                                                         env1));
                                                 (let uu____3012 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      (FStar_Options.Other
                                                         "LayeredEffects")
                                                     in
                                                  if uu____3012
                                                  then
                                                    let uu____3017 =
                                                      FStar_Syntax_Print.term_to_string
                                                        act_typ2
                                                       in
                                                    let uu____3019 =
                                                      FStar_Syntax_Print.term_to_string
                                                        expected_act_typ
                                                       in
                                                    let uu____3021 =
                                                      FStar_Syntax_Print.comp_to_string
                                                        repr_comp
                                                       in
                                                    FStar_Util.print4
                                                      "For action %s, act_typ: %s, expected_act_typ: %s, repr_comp: %s\n"
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                      uu____3017 uu____3019
                                                      uu____3021
                                                  else ());
                                                 (let expected_act_typ1 =
                                                    FStar_All.pipe_right
                                                      expected_act_typ
                                                      (FStar_TypeChecker_Normalize.normalize
                                                         [FStar_TypeChecker_Env.Beta]
                                                         env1)
                                                     in
                                                  let act_typ3 =
                                                    let uu____3028 =
                                                      let uu____3029 =
                                                        FStar_Syntax_Subst.compress
                                                          expected_act_typ1
                                                         in
                                                      uu____3029.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____3028 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs1,c) ->
                                                        let uu____3054 =
                                                          FStar_Syntax_Subst.open_comp
                                                            bs1 c
                                                           in
                                                        (match uu____3054
                                                         with
                                                         | (bs2,c1) ->
                                                             let uu____3061 =
                                                               let uu____3086
                                                                 =
                                                                 let uu____3087
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)
                                                                    FStar_Syntax_Subst.compress
                                                                    in
                                                                 uu____3087.FStar_Syntax_Syntax.n
                                                                  in
                                                               match uu____3086
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_app
                                                                   (hd1,t::args)
                                                                   ->
                                                                   let us =
                                                                    let uu____3160
                                                                    =
                                                                    let uu____3161
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____3161.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____3160
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uinst
                                                                    (uu____3164,us)
                                                                    -> []
                                                                    | 
                                                                    uu____3170
                                                                    -> []  in
                                                                   (us, t,
                                                                    args)
                                                               | uu____3189
                                                                   ->
                                                                   let uu____3190
                                                                    =
                                                                    let uu____3192
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    Prims.op_Hat
                                                                    "tc_layered_eff_decl: unexpected expected act_typ with comp_result: "
                                                                    uu____3192
                                                                     in
                                                                   failwith
                                                                    uu____3190
                                                                in
                                                             (match uu____3061
                                                              with
                                                              | (us,t,args)
                                                                  ->
                                                                  let c2 =
                                                                    let uu____3259
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____3259;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = args;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                  let uu____3276
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                  FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____3276))
                                                    | uu____3279 ->
                                                        failwith
                                                          "tc_layered_eff_decl: expected expected_act_typ to be an arrow"
                                                     in
                                                  (let uu____3282 =
                                                     FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env1)
                                                       (FStar_Options.Other
                                                          "LayeredEffects")
                                                      in
                                                   if uu____3282
                                                   then
                                                     let uu____3287 =
                                                       FStar_Syntax_Print.term_to_string
                                                         act_typ3
                                                        in
                                                     FStar_Util.print2
                                                       "After injecting into the monad, action %s has type %s\n"
                                                       (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                       uu____3287
                                                   else ());
                                                  (let uu____3292 =
                                                     if
                                                       (FStar_List.length
                                                          univs1)
                                                         = Prims.int_zero
                                                     then
                                                       FStar_TypeChecker_Util.generalize_universes
                                                         env01 act_defn
                                                     else
                                                       (let uu____3310 =
                                                          FStar_Syntax_Subst.close_univ_vars
                                                            univs1 act_defn
                                                           in
                                                        (univs1, uu____3310))
                                                      in
                                                   match uu____3292 with
                                                   | (univs2,act_defn1) ->
                                                       let act_typ4 =
                                                         let uu____3322 =
                                                           FStar_All.pipe_right
                                                             act_typ3
                                                             (FStar_TypeChecker_Normalize.normalize
                                                                [FStar_TypeChecker_Env.Beta]
                                                                env1)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____3322
                                                           (FStar_Syntax_Subst.close_univ_vars
                                                              univs2)
                                                          in
                                                       let uu___392_3323 =
                                                         act1  in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___392_3323.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___392_3323.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = univs2;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___392_3323.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = act_typ4
                                                       })))))))
                             in
                          let actions =
                            FStar_List.map (tc_action env)
                              ed2.FStar_Syntax_Syntax.actions
                             in
                          let uu____3327 =
                            let uu____3332 =
                              FStar_TypeChecker_Util.generalize_universes
                                env0 ed2.FStar_Syntax_Syntax.signature
                               in
                            match uu____3332 with
                            | (univs1,signature1) ->
                                (match annotated_univ_names with
                                 | [] -> (univs1, signature1)
                                 | uu____3351 ->
                                     let uu____3354 =
                                       ((FStar_List.length univs1) =
                                          (FStar_List.length
                                             annotated_univ_names))
                                         &&
                                         (FStar_List.forall2
                                            (fun u1  ->
                                               fun u2  ->
                                                 let uu____3361 =
                                                   FStar_Syntax_Syntax.order_univ_name
                                                     u1 u2
                                                    in
                                                 uu____3361 = Prims.int_zero)
                                            univs1 annotated_univ_names)
                                        in
                                     if uu____3354
                                     then (univs1, signature1)
                                     else
                                       (let uu____3372 =
                                          let uu____3378 =
                                            let uu____3380 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length
                                                   annotated_univ_names)
                                               in
                                            let uu____3382 =
                                              FStar_Util.string_of_int
                                                (FStar_List.length univs1)
                                               in
                                            FStar_Util.format2
                                              "Expected an effect definition with %s universes; but found %s"
                                              uu____3380 uu____3382
                                             in
                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                            uu____3378)
                                           in
                                        FStar_Errors.raise_error uu____3372
                                          (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                             in
                          (match uu____3327 with
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
                                 (let uu____3412 =
                                    ((n1 >= Prims.int_zero) &&
                                       (let uu____3416 =
                                          FStar_Syntax_Util.is_unknown
                                            (FStar_Pervasives_Native.snd ts1)
                                           in
                                        Prims.op_Negation uu____3416))
                                      && (m <> n1)
                                     in
                                  if uu____3412
                                  then
                                    let error =
                                      if m < n1
                                      then "not universe-polymorphic enough"
                                      else "too universe-polymorphic"  in
                                    let err_msg =
                                      let uu____3434 =
                                        FStar_Util.string_of_int m  in
                                      let uu____3436 =
                                        FStar_Util.string_of_int n1  in
                                      let uu____3438 =
                                        FStar_Syntax_Print.tscheme_to_string
                                          ts1
                                         in
                                      FStar_Util.format4
                                        "The effect combinator is %s (m,n=%s,%s) (%s)"
                                        error uu____3434 uu____3436
                                        uu____3438
                                       in
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                        err_msg)
                                      (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos
                                  else ());
                                 ts1  in
                               let ed3 =
                                 let uu___416_3449 = ed2  in
                                 let uu____3450 =
                                   close1 Prims.int_zero return_wp  in
                                 let uu____3452 =
                                   close1 Prims.int_one bind_wp  in
                                 let uu____3454 =
                                   close1 Prims.int_zero return_repr  in
                                 let uu____3456 =
                                   close1 Prims.int_one bind_repr  in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___416_3449.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___416_3449.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___416_3449.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs = univs1;
                                   FStar_Syntax_Syntax.binders = [];
                                   FStar_Syntax_Syntax.signature = signature1;
                                   FStar_Syntax_Syntax.ret_wp = uu____3450;
                                   FStar_Syntax_Syntax.bind_wp = uu____3452;
                                   FStar_Syntax_Syntax.stronger =
                                     (uu___416_3449.FStar_Syntax_Syntax.stronger);
                                   FStar_Syntax_Syntax.match_wps =
                                     (uu___416_3449.FStar_Syntax_Syntax.match_wps);
                                   FStar_Syntax_Syntax.trivial =
                                     (uu___416_3449.FStar_Syntax_Syntax.trivial);
                                   FStar_Syntax_Syntax.repr = repr;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____3454;
                                   FStar_Syntax_Syntax.bind_repr = uu____3456;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     (uu___416_3449.FStar_Syntax_Syntax.stronger_repr);
                                   FStar_Syntax_Syntax.actions = actions;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___416_3449.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____3465 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____3465
                                 then
                                   let uu____3470 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked layered effect: %s\n"
                                     uu____3470
                                 else ());
                                failwith "That's it for now!";
                                ed3))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      let uu____3489 =
        FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs  in
      match uu____3489 with
      | (open_annotated_univs,annotated_univ_names) ->
          let open_univs n_binders t =
            let uu____3521 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst uu____3521 t  in
          let open_univs_binders n_binders bs =
            let uu____3537 =
              FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs
               in
            FStar_Syntax_Subst.subst_binders uu____3537 bs  in
          let n_effect_params =
            FStar_List.length ed.FStar_Syntax_Syntax.binders  in
          let uu____3547 =
            let uu____3554 =
              open_univs_binders Prims.int_zero
                ed.FStar_Syntax_Syntax.binders
               in
            let uu____3556 =
              open_univs n_effect_params ed.FStar_Syntax_Syntax.signature  in
            FStar_Syntax_Subst.open_term' uu____3554 uu____3556  in
          (match uu____3547 with
           | (effect_params_un,signature_un,opening) ->
               let env =
                 FStar_TypeChecker_Env.push_univ_vars env0
                   annotated_univ_names
                  in
               let uu____3561 =
                 FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un  in
               (match uu____3561 with
                | (effect_params,env1,uu____3570) ->
                    let uu____3571 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                        signature_un
                       in
                    (match uu____3571 with
                     | (signature,uu____3577) ->
                         let ed1 =
                           let uu___446_3579 = ed  in
                           {
                             FStar_Syntax_Syntax.is_layered =
                               (uu___446_3579.FStar_Syntax_Syntax.is_layered);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___446_3579.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___446_3579.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs =
                               (uu___446_3579.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders = effect_params;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp =
                               (uu___446_3579.FStar_Syntax_Syntax.ret_wp);
                             FStar_Syntax_Syntax.bind_wp =
                               (uu___446_3579.FStar_Syntax_Syntax.bind_wp);
                             FStar_Syntax_Syntax.stronger =
                               (uu___446_3579.FStar_Syntax_Syntax.stronger);
                             FStar_Syntax_Syntax.match_wps =
                               (uu___446_3579.FStar_Syntax_Syntax.match_wps);
                             FStar_Syntax_Syntax.trivial =
                               (uu___446_3579.FStar_Syntax_Syntax.trivial);
                             FStar_Syntax_Syntax.repr =
                               (uu___446_3579.FStar_Syntax_Syntax.repr);
                             FStar_Syntax_Syntax.return_repr =
                               (uu___446_3579.FStar_Syntax_Syntax.return_repr);
                             FStar_Syntax_Syntax.bind_repr =
                               (uu___446_3579.FStar_Syntax_Syntax.bind_repr);
                             FStar_Syntax_Syntax.stronger_repr =
                               (uu___446_3579.FStar_Syntax_Syntax.stronger_repr);
                             FStar_Syntax_Syntax.actions =
                               (uu___446_3579.FStar_Syntax_Syntax.actions);
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___446_3579.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let ed2 =
                           match (effect_params, annotated_univ_names) with
                           | ([],[]) -> ed1
                           | uu____3607 ->
                               let op uu____3639 =
                                 match uu____3639 with
                                 | (us,t) ->
                                     let n_us = FStar_List.length us  in
                                     let uu____3659 =
                                       let uu____3660 =
                                         FStar_Syntax_Subst.shift_subst n_us
                                           opening
                                          in
                                       let uu____3663 = open_univs n_us t  in
                                       FStar_Syntax_Subst.subst uu____3660
                                         uu____3663
                                        in
                                     (us, uu____3659)
                                  in
                               let uu___458_3666 = ed1  in
                               let uu____3667 =
                                 op ed1.FStar_Syntax_Syntax.ret_wp  in
                               let uu____3668 =
                                 op ed1.FStar_Syntax_Syntax.bind_wp  in
                               let uu____3669 =
                                 op ed1.FStar_Syntax_Syntax.stronger  in
                               let uu____3670 =
                                 FStar_Syntax_Util.map_match_wps op
                                   ed1.FStar_Syntax_Syntax.match_wps
                                  in
                               let uu____3675 =
                                 FStar_Util.map_opt
                                   ed1.FStar_Syntax_Syntax.trivial op
                                  in
                               let uu____3678 =
                                 let uu____3679 =
                                   op ([], (ed1.FStar_Syntax_Syntax.repr))
                                    in
                                 FStar_Pervasives_Native.snd uu____3679  in
                               let uu____3690 =
                                 op ed1.FStar_Syntax_Syntax.return_repr  in
                               let uu____3691 =
                                 op ed1.FStar_Syntax_Syntax.bind_repr  in
                               let uu____3692 =
                                 FStar_List.map
                                   (fun a  ->
                                      let uu___461_3700 = a  in
                                      let uu____3701 =
                                        let uu____3702 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_defn))
                                           in
                                        FStar_Pervasives_Native.snd
                                          uu____3702
                                         in
                                      let uu____3713 =
                                        let uu____3714 =
                                          op
                                            ((a.FStar_Syntax_Syntax.action_univs),
                                              (a.FStar_Syntax_Syntax.action_typ))
                                           in
                                        FStar_Pervasives_Native.snd
                                          uu____3714
                                         in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___461_3700.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___461_3700.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          (uu___461_3700.FStar_Syntax_Syntax.action_univs);
                                        FStar_Syntax_Syntax.action_params =
                                          (uu___461_3700.FStar_Syntax_Syntax.action_params);
                                        FStar_Syntax_Syntax.action_defn =
                                          uu____3701;
                                        FStar_Syntax_Syntax.action_typ =
                                          uu____3713
                                      }) ed1.FStar_Syntax_Syntax.actions
                                  in
                               {
                                 FStar_Syntax_Syntax.is_layered =
                                   (uu___458_3666.FStar_Syntax_Syntax.is_layered);
                                 FStar_Syntax_Syntax.cattributes =
                                   (uu___458_3666.FStar_Syntax_Syntax.cattributes);
                                 FStar_Syntax_Syntax.mname =
                                   (uu___458_3666.FStar_Syntax_Syntax.mname);
                                 FStar_Syntax_Syntax.univs =
                                   annotated_univ_names;
                                 FStar_Syntax_Syntax.binders =
                                   (uu___458_3666.FStar_Syntax_Syntax.binders);
                                 FStar_Syntax_Syntax.signature =
                                   (uu___458_3666.FStar_Syntax_Syntax.signature);
                                 FStar_Syntax_Syntax.ret_wp = uu____3667;
                                 FStar_Syntax_Syntax.bind_wp = uu____3668;
                                 FStar_Syntax_Syntax.stronger = uu____3669;
                                 FStar_Syntax_Syntax.match_wps = uu____3670;
                                 FStar_Syntax_Syntax.trivial = uu____3675;
                                 FStar_Syntax_Syntax.repr = uu____3678;
                                 FStar_Syntax_Syntax.return_repr = uu____3690;
                                 FStar_Syntax_Syntax.bind_repr = uu____3691;
                                 FStar_Syntax_Syntax.stronger_repr =
                                   (uu___458_3666.FStar_Syntax_Syntax.stronger_repr);
                                 FStar_Syntax_Syntax.actions = uu____3692;
                                 FStar_Syntax_Syntax.eff_attrs =
                                   (uu___458_3666.FStar_Syntax_Syntax.eff_attrs)
                               }
                            in
                         let wp_with_fresh_result_type env2 mname signature1
                           =
                           let fail1 t =
                             let uu____3759 =
                               FStar_TypeChecker_Err.unexpected_signature_for_monad
                                 env2 mname t
                                in
                             let uu____3765 = FStar_Ident.range_of_lid mname
                                in
                             FStar_Errors.raise_error uu____3759 uu____3765
                              in
                           let uu____3772 =
                             let uu____3773 =
                               FStar_Syntax_Subst.compress signature1  in
                             uu____3773.FStar_Syntax_Syntax.n  in
                           match uu____3772 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs
                                  in
                               (match bs1 with
                                | (a,uu____3812)::(wp,uu____3814)::[] ->
                                    (a, (wp.FStar_Syntax_Syntax.sort))
                                | uu____3843 -> fail1 signature1)
                           | uu____3844 -> fail1 signature1  in
                         let uu____3845 =
                           wp_with_fresh_result_type env1
                             ed2.FStar_Syntax_Syntax.mname
                             ed2.FStar_Syntax_Syntax.signature
                            in
                         (match uu____3845 with
                          | (a,wp_a) ->
                              let fresh_effect_signature uu____3869 =
                                match annotated_univ_names with
                                | [] ->
                                    let uu____3876 =
                                      FStar_TypeChecker_TcTerm.tc_trivial_guard
                                        env1 signature_un
                                       in
                                    (match uu____3876 with
                                     | (signature1,uu____3888) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                | uu____3889 ->
                                    let uu____3892 =
                                      let uu____3897 =
                                        let uu____3898 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            annotated_univ_names signature
                                           in
                                        (annotated_univ_names, uu____3898)
                                         in
                                      FStar_TypeChecker_Env.inst_tscheme
                                        uu____3897
                                       in
                                    (match uu____3892 with
                                     | (uu____3911,signature1) ->
                                         wp_with_fresh_result_type env1
                                           ed2.FStar_Syntax_Syntax.mname
                                           signature1)
                                 in
                              let env2 =
                                let uu____3914 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None
                                    ed2.FStar_Syntax_Syntax.signature
                                   in
                                FStar_TypeChecker_Env.push_bv env1 uu____3914
                                 in
                              ((let uu____3916 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____3916
                                then
                                  let uu____3921 =
                                    FStar_Syntax_Print.lid_to_string
                                      ed2.FStar_Syntax_Syntax.mname
                                     in
                                  let uu____3923 =
                                    FStar_Syntax_Print.binders_to_string " "
                                      ed2.FStar_Syntax_Syntax.binders
                                     in
                                  let uu____3926 =
                                    FStar_Syntax_Print.term_to_string
                                      ed2.FStar_Syntax_Syntax.signature
                                     in
                                  let uu____3928 =
                                    let uu____3930 =
                                      FStar_Syntax_Syntax.bv_to_name a  in
                                    FStar_Syntax_Print.term_to_string
                                      uu____3930
                                     in
                                  let uu____3931 =
                                    FStar_Syntax_Print.term_to_string
                                      a.FStar_Syntax_Syntax.sort
                                     in
                                  FStar_Util.print5
                                    "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                    uu____3921 uu____3923 uu____3926
                                    uu____3928 uu____3931
                                else ());
                               (let check_and_gen' env3 uu____3966 k =
                                  match uu____3966 with
                                  | (us,t) ->
                                      (match annotated_univ_names with
                                       | [] -> check_and_gen env3 t k
                                       | uu____4002::uu____4003 ->
                                           let uu____4006 =
                                             FStar_Syntax_Subst.subst_tscheme
                                               open_annotated_univs (us, t)
                                              in
                                           (match uu____4006 with
                                            | (us1,t1) ->
                                                let uu____4029 =
                                                  FStar_Syntax_Subst.open_univ_vars
                                                    us1 t1
                                                   in
                                                (match uu____4029 with
                                                 | (us2,t2) ->
                                                     let uu____4044 =
                                                       let uu____4045 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env3 us2
                                                          in
                                                       tc_check_trivial_guard
                                                         uu____4045 t2 k
                                                        in
                                                     let uu____4046 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         us2 t2
                                                        in
                                                     (us2, uu____4046))))
                                   in
                                let return_wp =
                                  let expected_k =
                                    let uu____4065 =
                                      let uu____4074 =
                                        FStar_Syntax_Syntax.mk_binder a  in
                                      let uu____4081 =
                                        let uu____4090 =
                                          let uu____4097 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____4097
                                           in
                                        [uu____4090]  in
                                      uu____4074 :: uu____4081  in
                                    let uu____4116 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_a  in
                                    FStar_Syntax_Util.arrow uu____4065
                                      uu____4116
                                     in
                                  check_and_gen' env2
                                    ed2.FStar_Syntax_Syntax.ret_wp expected_k
                                   in
                                let bind_wp =
                                  let uu____4120 = fresh_effect_signature ()
                                     in
                                  match uu____4120 with
                                  | (b,wp_b) ->
                                      let a_wp_b =
                                        let uu____4136 =
                                          let uu____4145 =
                                            let uu____4152 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4152
                                             in
                                          [uu____4145]  in
                                        let uu____4165 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____4136
                                          uu____4165
                                         in
                                      let expected_k =
                                        let uu____4171 =
                                          let uu____4180 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____4187 =
                                            let uu____4196 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____4203 =
                                              let uu____4212 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____4219 =
                                                let uu____4228 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4235 =
                                                  let uu____4244 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      a_wp_b
                                                     in
                                                  [uu____4244]  in
                                                uu____4228 :: uu____4235  in
                                              uu____4212 :: uu____4219  in
                                            uu____4196 :: uu____4203  in
                                          uu____4180 :: uu____4187  in
                                        let uu____4287 =
                                          FStar_Syntax_Syntax.mk_Total wp_b
                                           in
                                        FStar_Syntax_Util.arrow uu____4171
                                          uu____4287
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        expected_k
                                   in
                                let uu____4290 =
                                  FStar_Syntax_Util.get_match_with_close_wps
                                    ed2.FStar_Syntax_Syntax.match_wps
                                   in
                                match uu____4290 with
                                | (if_then_else1,ite_wp,close_wp) ->
                                    let if_then_else2 =
                                      let p =
                                        let uu____4310 =
                                          let uu____4313 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4313
                                           in
                                        let uu____4314 =
                                          let uu____4315 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4315
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4310
                                          uu____4314
                                         in
                                      let expected_k =
                                        let uu____4327 =
                                          let uu____4336 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4343 =
                                            let uu____4352 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4359 =
                                              let uu____4368 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4375 =
                                                let uu____4384 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4384]  in
                                              uu____4368 :: uu____4375  in
                                            uu____4352 :: uu____4359  in
                                          uu____4336 :: uu____4343  in
                                        let uu____4421 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4327
                                          uu____4421
                                         in
                                      check_and_gen' env2 if_then_else1
                                        expected_k
                                       in
                                    let ite_wp1 =
                                      let expected_k =
                                        let uu____4436 =
                                          let uu____4445 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4452 =
                                            let uu____4461 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4461]  in
                                          uu____4445 :: uu____4452  in
                                        let uu____4486 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4436
                                          uu____4486
                                         in
                                      check_and_gen' env2 ite_wp expected_k
                                       in
                                    let close_wp1 =
                                      let b =
                                        let uu____4499 =
                                          let uu____4502 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4502
                                           in
                                        let uu____4503 =
                                          let uu____4504 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4504
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4499
                                          uu____4503
                                         in
                                      let b_wp_a =
                                        let uu____4516 =
                                          let uu____4525 =
                                            let uu____4532 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4532
                                             in
                                          [uu____4525]  in
                                        let uu____4545 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4516
                                          uu____4545
                                         in
                                      let expected_k =
                                        let uu____4551 =
                                          let uu____4560 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4567 =
                                            let uu____4576 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4583 =
                                              let uu____4592 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4592]  in
                                            uu____4576 :: uu____4583  in
                                          uu____4560 :: uu____4567  in
                                        let uu____4623 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4551
                                          uu____4623
                                         in
                                      check_and_gen' env2 close_wp expected_k
                                       in
                                    let stronger =
                                      let uu____4627 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4627 with
                                      | (t,uu____4633) ->
                                          let expected_k =
                                            let uu____4637 =
                                              let uu____4646 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4653 =
                                                let uu____4662 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4669 =
                                                  let uu____4678 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4678]  in
                                                uu____4662 :: uu____4669  in
                                              uu____4646 :: uu____4653  in
                                            let uu____4709 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4637 uu____4709
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
                                          let uu____4718 =
                                            FStar_Syntax_Util.type_u ()  in
                                          (match uu____4718 with
                                           | (t,uu____4726) ->
                                               let expected_k =
                                                 let uu____4730 =
                                                   let uu____4739 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       a
                                                      in
                                                   let uu____4746 =
                                                     let uu____4755 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         wp_a
                                                        in
                                                     [uu____4755]  in
                                                   uu____4739 :: uu____4746
                                                    in
                                                 let uu____4780 =
                                                   FStar_Syntax_Syntax.mk_GTotal
                                                     t
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____4730 uu____4780
                                                  in
                                               let uu____4783 =
                                                 check_and_gen' env2 trivial
                                                   expected_k
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____4783)
                                       in
                                    let uu____4784 =
                                      let uu____4797 =
                                        let uu____4798 =
                                          FStar_Syntax_Subst.compress
                                            ed2.FStar_Syntax_Syntax.repr
                                           in
                                        uu____4798.FStar_Syntax_Syntax.n  in
                                      match uu____4797 with
                                      | FStar_Syntax_Syntax.Tm_unknown  ->
                                          ((ed2.FStar_Syntax_Syntax.repr),
                                            (ed2.FStar_Syntax_Syntax.bind_repr),
                                            (ed2.FStar_Syntax_Syntax.return_repr),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                      | uu____4817 ->
                                          let repr =
                                            let uu____4819 =
                                              FStar_Syntax_Util.type_u ()  in
                                            match uu____4819 with
                                            | (t,uu____4825) ->
                                                let expected_k =
                                                  let uu____4829 =
                                                    let uu____4838 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____4845 =
                                                      let uu____4854 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_a
                                                         in
                                                      [uu____4854]  in
                                                    uu____4838 :: uu____4845
                                                     in
                                                  let uu____4879 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____4829 uu____4879
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
                                            let uu____4896 =
                                              let uu____4903 =
                                                let uu____4904 =
                                                  let uu____4921 =
                                                    let uu____4932 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    let uu____4941 =
                                                      let uu____4952 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          wp
                                                         in
                                                      [uu____4952]  in
                                                    uu____4932 :: uu____4941
                                                     in
                                                  (repr1, uu____4921)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____4904
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____4903
                                               in
                                            uu____4896
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let mk_repr a1 wp =
                                            let uu____5010 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            mk_repr' uu____5010 wp  in
                                          let destruct_repr t =
                                            let uu____5025 =
                                              let uu____5026 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____5026.FStar_Syntax_Syntax.n
                                               in
                                            match uu____5025 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____5037,(t1,uu____5039)::
                                                 (wp,uu____5041)::[])
                                                -> (t1, wp)
                                            | uu____5100 ->
                                                failwith
                                                  "Unexpected repr type"
                                             in
                                          let bind_repr =
                                            let r =
                                              let uu____5112 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  FStar_Parser_Const.range_0
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_All.pipe_right uu____5112
                                                FStar_Syntax_Syntax.fv_to_tm
                                               in
                                            let uu____5113 =
                                              fresh_effect_signature ()  in
                                            match uu____5113 with
                                            | (b,wp_b) ->
                                                let a_wp_b =
                                                  let uu____5129 =
                                                    let uu____5138 =
                                                      let uu____5145 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____5145
                                                       in
                                                    [uu____5138]  in
                                                  let uu____5158 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      wp_b
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5129 uu____5158
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
                                                  let uu____5166 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____5166
                                                   in
                                                let wp_g_x =
                                                  let uu____5171 =
                                                    let uu____5176 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        wp_g
                                                       in
                                                    let uu____5177 =
                                                      let uu____5178 =
                                                        let uu____5187 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5187
                                                         in
                                                      [uu____5178]  in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5176 uu____5177
                                                     in
                                                  uu____5171
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                let res =
                                                  let wp =
                                                    let uu____5218 =
                                                      let uu____5223 =
                                                        let uu____5224 =
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            bind_wp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5224
                                                          FStar_Pervasives_Native.snd
                                                         in
                                                      let uu____5233 =
                                                        let uu____5234 =
                                                          let uu____5237 =
                                                            let uu____5240 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a
                                                               in
                                                            let uu____5241 =
                                                              let uu____5244
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b
                                                                 in
                                                              let uu____5245
                                                                =
                                                                let uu____5248
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                   in
                                                                let uu____5249
                                                                  =
                                                                  let uu____5252
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                  [uu____5252]
                                                                   in
                                                                uu____5248 ::
                                                                  uu____5249
                                                                 in
                                                              uu____5244 ::
                                                                uu____5245
                                                               in
                                                            uu____5240 ::
                                                              uu____5241
                                                             in
                                                          r :: uu____5237  in
                                                        FStar_List.map
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5234
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____5223 uu____5233
                                                       in
                                                    uu____5218
                                                      FStar_Pervasives_Native.None
                                                      FStar_Range.dummyRange
                                                     in
                                                  mk_repr b wp  in
                                                let maybe_range_arg =
                                                  let uu____5270 =
                                                    FStar_Util.for_some
                                                      (FStar_Syntax_Util.attr_eq
                                                         FStar_Syntax_Util.dm4f_bind_range_attr)
                                                      ed2.FStar_Syntax_Syntax.eff_attrs
                                                     in
                                                  if uu____5270
                                                  then
                                                    let uu____5281 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    let uu____5288 =
                                                      let uu____5297 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          FStar_Syntax_Syntax.t_range
                                                         in
                                                      [uu____5297]  in
                                                    uu____5281 :: uu____5288
                                                  else []  in
                                                let expected_k =
                                                  let uu____5333 =
                                                    let uu____5342 =
                                                      let uu____5351 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let uu____5358 =
                                                        let uu____5367 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            b
                                                           in
                                                        [uu____5367]  in
                                                      uu____5351 ::
                                                        uu____5358
                                                       in
                                                    let uu____5392 =
                                                      let uu____5401 =
                                                        let uu____5410 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_f
                                                           in
                                                        let uu____5417 =
                                                          let uu____5426 =
                                                            let uu____5433 =
                                                              let uu____5434
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              mk_repr a
                                                                uu____5434
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____5433
                                                             in
                                                          let uu____5435 =
                                                            let uu____5444 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_g
                                                               in
                                                            let uu____5451 =
                                                              let uu____5460
                                                                =
                                                                let uu____5467
                                                                  =
                                                                  let uu____5468
                                                                    =
                                                                    let uu____5477
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____5477]
                                                                     in
                                                                  let uu____5496
                                                                    =
                                                                    let uu____5499
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5499
                                                                     in
                                                                  FStar_Syntax_Util.arrow
                                                                    uu____5468
                                                                    uu____5496
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____5467
                                                                 in
                                                              [uu____5460]
                                                               in
                                                            uu____5444 ::
                                                              uu____5451
                                                             in
                                                          uu____5426 ::
                                                            uu____5435
                                                           in
                                                        uu____5410 ::
                                                          uu____5417
                                                         in
                                                      FStar_List.append
                                                        maybe_range_arg
                                                        uu____5401
                                                       in
                                                    FStar_List.append
                                                      uu____5342 uu____5392
                                                     in
                                                  let uu____5544 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5333 uu____5544
                                                   in
                                                let uu____5547 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                (match uu____5547 with
                                                 | (expected_k1,uu____5555,uu____5556)
                                                     ->
                                                     let env3 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env2
                                                         (FStar_Pervasives_Native.snd
                                                            ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                        in
                                                     let env4 =
                                                       let uu___597_5563 =
                                                         env3  in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.instantiate_imp);
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           = true;
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___597_5563.FStar_TypeChecker_Env.strict_args_tab)
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
                                              let uu____5576 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____5576
                                               in
                                            let res =
                                              let wp =
                                                let uu____5584 =
                                                  let uu____5589 =
                                                    let uu____5590 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        return_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____5590
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____5599 =
                                                    let uu____5600 =
                                                      let uu____5603 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____5604 =
                                                        let uu____5607 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        [uu____5607]  in
                                                      uu____5603 ::
                                                        uu____5604
                                                       in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____5600
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5589 uu____5599
                                                   in
                                                uu____5584
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr a wp  in
                                            let expected_k =
                                              let uu____5619 =
                                                let uu____5628 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5635 =
                                                  let uu____5644 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x_a
                                                     in
                                                  [uu____5644]  in
                                                uu____5628 :: uu____5635  in
                                              let uu____5669 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5619 uu____5669
                                               in
                                            let uu____5672 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            match uu____5672 with
                                            | (expected_k1,uu____5680,uu____5681)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env2
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                let uu____5687 =
                                                  check_and_gen' env3
                                                    ed2.FStar_Syntax_Syntax.return_repr
                                                    expected_k1
                                                   in
                                                (match uu____5687 with
                                                 | (univs1,repr1) ->
                                                     (match univs1 with
                                                      | [] -> ([], repr1)
                                                      | uu____5710 ->
                                                          FStar_Errors.raise_error
                                                            (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                              "Unexpected universe-polymorphic return for effect")
                                                            repr1.FStar_Syntax_Syntax.pos))
                                             in
                                          let actions =
                                            let check_action act =
                                              let uu____5725 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env2, act)
                                                else
                                                  (let uu____5739 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____5739 with
                                                   | (usubst,uvs) ->
                                                       let uu____5762 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env2 uvs
                                                          in
                                                       let uu____5763 =
                                                         let uu___626_5764 =
                                                           act  in
                                                         let uu____5765 =
                                                           FStar_Syntax_Subst.subst_binders
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_params
                                                            in
                                                         let uu____5766 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____5767 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___626_5764.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___626_5764.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             = uu____5765;
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____5766;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____5767
                                                         }  in
                                                       (uu____5762,
                                                         uu____5763))
                                                 in
                                              match uu____5725 with
                                              | (env3,act1) ->
                                                  let act_typ =
                                                    let uu____5771 =
                                                      let uu____5772 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____5772.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____5771 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____5798 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____5798
                                                        then
                                                          let uu____5801 =
                                                            let uu____5804 =
                                                              let uu____5805
                                                                =
                                                                let uu____5806
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____5806
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____5805
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____5804
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs uu____5801
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____5829 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____5830 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env3 act_typ
                                                     in
                                                  (match uu____5830 with
                                                   | (act_typ1,uu____5838,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___643_5841 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env3 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___643_5841.FStar_TypeChecker_Env.strict_args_tab)
                                                         }  in
                                                       ((let uu____5844 =
                                                           FStar_TypeChecker_Env.debug
                                                             env3
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____5844
                                                         then
                                                           let uu____5848 =
                                                             FStar_Ident.text_of_lid
                                                               act1.FStar_Syntax_Syntax.action_name
                                                              in
                                                           let uu____5850 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act1.FStar_Syntax_Syntax.action_defn
                                                              in
                                                           let uu____5852 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ1
                                                              in
                                                           FStar_Util.print3
                                                             "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                             uu____5848
                                                             uu____5850
                                                             uu____5852
                                                         else ());
                                                        (let uu____5857 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____5857
                                                         with
                                                         | (act_defn,uu____5865,g_a)
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
                                                             let uu____5869 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c) ->
                                                                   let uu____5905
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____5905
                                                                    with
                                                                    | 
                                                                    (bs1,uu____5917)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____5924
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____5924
                                                                     in
                                                                    let uu____5927
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____5927
                                                                    with
                                                                    | 
                                                                    (k1,uu____5941,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____5945
                                                                   ->
                                                                   let uu____5946
                                                                    =
                                                                    let uu____5952
                                                                    =
                                                                    let uu____5954
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____5956
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____5954
                                                                    uu____5956
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____5952)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____5946
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____5869
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____5974
                                                                    =
                                                                    let uu____5975
                                                                    =
                                                                    let uu____5976
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____5976
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____5975
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____5974);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____5978
                                                                    =
                                                                    let uu____5979
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____5979.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5978
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____6004
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____6004
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____6011
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6011
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6031
                                                                    =
                                                                    let uu____6032
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6032]
                                                                     in
                                                                    let uu____6033
                                                                    =
                                                                    let uu____6044
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6044]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6031;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6033;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6069
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6069))
                                                                    | 
                                                                    uu____6072
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____6074
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6096
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6096))
                                                                     in
                                                                    match uu____6074
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
                                                                    let uu___693_6115
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___693_6115.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___693_6115.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___693_6115.FStar_Syntax_Syntax.action_params);
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
                                    (match uu____4784 with
                                     | (repr,bind_repr,return_repr,actions)
                                         ->
                                         let t0 =
                                           let uu____6139 =
                                             FStar_Syntax_Syntax.mk_Total
                                               ed2.FStar_Syntax_Syntax.signature
                                              in
                                           FStar_Syntax_Util.arrow
                                             ed2.FStar_Syntax_Syntax.binders
                                             uu____6139
                                            in
                                         let uu____6142 =
                                           let uu____6147 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env0 t0
                                              in
                                           match uu____6147 with
                                           | (gen_univs,t) ->
                                               (match annotated_univ_names
                                                with
                                                | [] -> (gen_univs, t)
                                                | uu____6166 ->
                                                    let uu____6169 =
                                                      ((FStar_List.length
                                                          gen_univs)
                                                         =
                                                         (FStar_List.length
                                                            annotated_univ_names))
                                                        &&
                                                        (FStar_List.forall2
                                                           (fun u1  ->
                                                              fun u2  ->
                                                                let uu____6176
                                                                  =
                                                                  FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2
                                                                   in
                                                                uu____6176 =
                                                                  Prims.int_zero)
                                                           gen_univs
                                                           annotated_univ_names)
                                                       in
                                                    if uu____6169
                                                    then (gen_univs, t)
                                                    else
                                                      (let uu____6187 =
                                                         let uu____6193 =
                                                           let uu____6195 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  annotated_univ_names)
                                                              in
                                                           let uu____6197 =
                                                             FStar_Util.string_of_int
                                                               (FStar_List.length
                                                                  gen_univs)
                                                              in
                                                           FStar_Util.format2
                                                             "Expected an effect definition with %s universes; but found %s"
                                                             uu____6195
                                                             uu____6197
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                           uu____6193)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____6187
                                                         (ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos))
                                            in
                                         (match uu____6142 with
                                          | (univs1,t) ->
                                              let signature1 =
                                                let uu____6208 =
                                                  let uu____6221 =
                                                    let uu____6222 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____6222.FStar_Syntax_Syntax.n
                                                     in
                                                  (effect_params, uu____6221)
                                                   in
                                                match uu____6208 with
                                                | ([],uu____6233) -> t
                                                | (uu____6248,FStar_Syntax_Syntax.Tm_arrow
                                                   (uu____6249,c)) ->
                                                    FStar_Syntax_Util.comp_result
                                                      c
                                                | uu____6287 ->
                                                    failwith
                                                      "Impossible : t is an arrow"
                                                 in
                                              let close1 n1 ts =
                                                let ts1 =
                                                  let uu____6315 =
                                                    FStar_Syntax_Subst.close_tscheme
                                                      effect_params ts
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars_tscheme
                                                    univs1 uu____6315
                                                   in
                                                let m =
                                                  FStar_List.length
                                                    (FStar_Pervasives_Native.fst
                                                       ts1)
                                                   in
                                                (let uu____6322 =
                                                   ((n1 >= Prims.int_zero) &&
                                                      (let uu____6326 =
                                                         FStar_Syntax_Util.is_unknown
                                                           (FStar_Pervasives_Native.snd
                                                              ts1)
                                                          in
                                                       Prims.op_Negation
                                                         uu____6326))
                                                     && (m <> n1)
                                                    in
                                                 if uu____6322
                                                 then
                                                   let error =
                                                     if m < n1
                                                     then
                                                       "not universe-polymorphic enough"
                                                     else
                                                       "too universe-polymorphic"
                                                      in
                                                   let err_msg =
                                                     let uu____6344 =
                                                       FStar_Util.string_of_int
                                                         m
                                                        in
                                                     let uu____6346 =
                                                       FStar_Util.string_of_int
                                                         n1
                                                        in
                                                     let uu____6348 =
                                                       FStar_Syntax_Print.tscheme_to_string
                                                         ts1
                                                        in
                                                     FStar_Util.format4
                                                       "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                       error uu____6344
                                                       uu____6346 uu____6348
                                                      in
                                                   FStar_Errors.raise_error
                                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                       err_msg)
                                                     (FStar_Pervasives_Native.snd
                                                        ts1).FStar_Syntax_Syntax.pos
                                                 else ());
                                                ts1  in
                                              let close_action act =
                                                let uu____6364 =
                                                  close1 (~- Prims.int_one)
                                                    ((act.FStar_Syntax_Syntax.action_univs),
                                                      (act.FStar_Syntax_Syntax.action_defn))
                                                   in
                                                match uu____6364 with
                                                | (univs2,defn) ->
                                                    let uu____6380 =
                                                      close1
                                                        (~- Prims.int_one)
                                                        ((act.FStar_Syntax_Syntax.action_univs),
                                                          (act.FStar_Syntax_Syntax.action_typ))
                                                       in
                                                    (match uu____6380 with
                                                     | (univs',typ) ->
                                                         let uu___743_6397 =
                                                           act  in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___743_6397.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___743_6397.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = univs2;
                                                           FStar_Syntax_Syntax.action_params
                                                             =
                                                             (uu___743_6397.FStar_Syntax_Syntax.action_params);
                                                           FStar_Syntax_Syntax.action_defn
                                                             = defn;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = typ
                                                         })
                                                 in
                                              let match_wps =
                                                let uu____6404 =
                                                  let uu____6405 =
                                                    close1 Prims.int_zero
                                                      if_then_else2
                                                     in
                                                  let uu____6407 =
                                                    close1 Prims.int_zero
                                                      ite_wp1
                                                     in
                                                  let uu____6409 =
                                                    close1 Prims.int_one
                                                      close_wp1
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.if_then_else
                                                      = uu____6405;
                                                    FStar_Syntax_Syntax.ite_wp
                                                      = uu____6407;
                                                    FStar_Syntax_Syntax.close_wp
                                                      = uu____6409
                                                  }  in
                                                FStar_Util.Inl uu____6404  in
                                              let ed3 =
                                                let uu___747_6412 = ed2  in
                                                let uu____6413 =
                                                  close1 Prims.int_zero
                                                    return_wp
                                                   in
                                                let uu____6415 =
                                                  close1 Prims.int_one
                                                    bind_wp
                                                   in
                                                let uu____6417 =
                                                  close1 Prims.int_zero
                                                    stronger
                                                   in
                                                let uu____6419 =
                                                  FStar_Util.map_opt
                                                    trivial_wp
                                                    (close1 Prims.int_zero)
                                                   in
                                                let uu____6423 =
                                                  let uu____6424 =
                                                    close1 Prims.int_zero
                                                      ([], repr)
                                                     in
                                                  FStar_Pervasives_Native.snd
                                                    uu____6424
                                                   in
                                                let uu____6442 =
                                                  close1 Prims.int_zero
                                                    return_repr
                                                   in
                                                let uu____6444 =
                                                  close1 Prims.int_one
                                                    bind_repr
                                                   in
                                                let uu____6446 =
                                                  FStar_List.map close_action
                                                    actions
                                                   in
                                                {
                                                  FStar_Syntax_Syntax.is_layered
                                                    =
                                                    (uu___747_6412.FStar_Syntax_Syntax.is_layered);
                                                  FStar_Syntax_Syntax.cattributes
                                                    =
                                                    (uu___747_6412.FStar_Syntax_Syntax.cattributes);
                                                  FStar_Syntax_Syntax.mname =
                                                    (uu___747_6412.FStar_Syntax_Syntax.mname);
                                                  FStar_Syntax_Syntax.univs =
                                                    univs1;
                                                  FStar_Syntax_Syntax.binders
                                                    = effect_params;
                                                  FStar_Syntax_Syntax.signature
                                                    = signature1;
                                                  FStar_Syntax_Syntax.ret_wp
                                                    = uu____6413;
                                                  FStar_Syntax_Syntax.bind_wp
                                                    = uu____6415;
                                                  FStar_Syntax_Syntax.stronger
                                                    = uu____6417;
                                                  FStar_Syntax_Syntax.match_wps
                                                    = match_wps;
                                                  FStar_Syntax_Syntax.trivial
                                                    = uu____6419;
                                                  FStar_Syntax_Syntax.repr =
                                                    uu____6423;
                                                  FStar_Syntax_Syntax.return_repr
                                                    = uu____6442;
                                                  FStar_Syntax_Syntax.bind_repr
                                                    = uu____6444;
                                                  FStar_Syntax_Syntax.stronger_repr
                                                    =
                                                    (uu___747_6412.FStar_Syntax_Syntax.stronger_repr);
                                                  FStar_Syntax_Syntax.actions
                                                    = uu____6446;
                                                  FStar_Syntax_Syntax.eff_attrs
                                                    =
                                                    (uu___747_6412.FStar_Syntax_Syntax.eff_attrs)
                                                }  in
                                              ((let uu____6450 =
                                                  (FStar_TypeChecker_Env.debug
                                                     env2 FStar_Options.Low)
                                                    ||
                                                    (FStar_All.pipe_left
                                                       (FStar_TypeChecker_Env.debug
                                                          env2)
                                                       (FStar_Options.Other
                                                          "ED"))
                                                   in
                                                if uu____6450
                                                then
                                                  let uu____6455 =
                                                    FStar_Syntax_Print.eff_decl_to_string
                                                      false ed3
                                                     in
                                                  FStar_Util.print_string
                                                    uu____6455
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
      let uu____6481 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____6481 with
      | (effect_binders_un,signature_un) ->
          let uu____6498 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____6498 with
           | (effect_binders,env1,uu____6517) ->
               let uu____6518 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____6518 with
                | (signature,uu____6534) ->
                    let raise_error1 uu____6550 =
                      match uu____6550 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____6586  ->
                           match uu____6586 with
                           | (bv,qual) ->
                               let uu____6605 =
                                 let uu___772_6606 = bv  in
                                 let uu____6607 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___772_6606.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___772_6606.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____6607
                                 }  in
                               (uu____6605, qual)) effect_binders
                       in
                    let uu____6612 =
                      let uu____6619 =
                        let uu____6620 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____6620.FStar_Syntax_Syntax.n  in
                      match uu____6619 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____6630)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____6662 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____6612 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____6688 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____6688
                           then
                             let uu____6691 =
                               let uu____6694 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____6694  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____6691
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____6742 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____6742 with
                           | (t2,comp,uu____6755) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____6764 =
                           open_and_check env1 [] ed.FStar_Syntax_Syntax.repr
                            in
                         (match uu____6764 with
                          | (repr,_comp) ->
                              ((let uu____6788 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____6788
                                then
                                  let uu____6792 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____6792
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
                                let uu____6799 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____6802 =
                                    let uu____6803 =
                                      let uu____6804 =
                                        let uu____6821 =
                                          let uu____6832 =
                                            let uu____6841 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____6844 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____6841, uu____6844)  in
                                          [uu____6832]  in
                                        (wp_type, uu____6821)  in
                                      FStar_Syntax_Syntax.Tm_app uu____6804
                                       in
                                    mk1 uu____6803  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____6802
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____6892 =
                                      let uu____6899 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____6899)  in
                                    let uu____6905 =
                                      let uu____6914 =
                                        let uu____6921 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____6921
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____6914]  in
                                    uu____6892 :: uu____6905  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____6958 =
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
                                  let uu____7024 = item  in
                                  match uu____7024 with
                                  | (u_item,item1) ->
                                      let uu____7039 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____7039 with
                                       | (item2,item_comp) ->
                                           ((let uu____7055 =
                                               let uu____7057 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____7057
                                                in
                                             if uu____7055
                                             then
                                               let uu____7060 =
                                                 let uu____7066 =
                                                   let uu____7068 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____7070 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____7068 uu____7070
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____7066)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____7060
                                             else ());
                                            (let uu____7076 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____7076 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____7094 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____7096 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____7098 =
                                  elaborate_and_star dmff_env []
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____7098 with
                                | (dmff_env1,uu____7124,bind_wp,bind_elab) ->
                                    let uu____7127 =
                                      elaborate_and_star dmff_env1 []
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____7127 with
                                     | (dmff_env2,uu____7153,return_wp,return_elab)
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
                                           let uu____7162 =
                                             let uu____7163 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____7163.FStar_Syntax_Syntax.n
                                              in
                                           match uu____7162 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____7221 =
                                                 let uu____7240 =
                                                   let uu____7245 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____7245
                                                    in
                                                 match uu____7240 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____7327 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____7221 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____7381 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____7381 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____7404 =
                                                          let uu____7405 =
                                                            let uu____7422 =
                                                              let uu____7433
                                                                =
                                                                let uu____7442
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____7447
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____7442,
                                                                  uu____7447)
                                                                 in
                                                              [uu____7433]
                                                               in
                                                            (wp_type,
                                                              uu____7422)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____7405
                                                           in
                                                        mk1 uu____7404  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____7483 =
                                                      let uu____7492 =
                                                        let uu____7493 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____7493
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____7492
                                                       in
                                                    (match uu____7483 with
                                                     | (bs1,body2,what') ->
                                                         let fail1 uu____7516
                                                           =
                                                           let error_msg =
                                                             let uu____7519 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____7521 =
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
                                                               uu____7519
                                                               uu____7521
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
                                                               ((let uu____7531
                                                                   =
                                                                   let uu____7533
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____7533
                                                                    in
                                                                 if
                                                                   uu____7531
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____7538
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
                                                                   uu____7538
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
                                                             let uu____7567 =
                                                               let uu____7572
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____7573
                                                                 =
                                                                 let uu____7574
                                                                   =
                                                                   let uu____7583
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____7583,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____7574]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____7572
                                                                 uu____7573
                                                                in
                                                             uu____7567
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____7618 =
                                                             let uu____7619 =
                                                               let uu____7628
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____7628]
                                                                in
                                                             b11 ::
                                                               uu____7619
                                                              in
                                                           let uu____7653 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____7618
                                                             uu____7653
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____7656 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____7664 =
                                             let uu____7665 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____7665.FStar_Syntax_Syntax.n
                                              in
                                           match uu____7664 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____7723 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____7723
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____7744 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____7752 =
                                             let uu____7753 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____7753.FStar_Syntax_Syntax.n
                                              in
                                           match uu____7752 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____7787 =
                                                 let uu____7788 =
                                                   let uu____7797 =
                                                     let uu____7804 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____7804
                                                      in
                                                   [uu____7797]  in
                                                 FStar_List.append uu____7788
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____7787 body what
                                           | uu____7823 ->
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
                                             (let uu____7853 =
                                                let uu____7854 =
                                                  let uu____7855 =
                                                    let uu____7872 =
                                                      let uu____7883 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____7883
                                                       in
                                                    (t, uu____7872)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____7855
                                                   in
                                                mk1 uu____7854  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____7853)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____7941 = f a2  in
                                               [uu____7941]
                                           | x::xs ->
                                               let uu____7952 =
                                                 apply_last1 f xs  in
                                               x :: uu____7952
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
                                           let uu____7986 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____7986 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____8016 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____8016
                                                 then
                                                   let uu____8019 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____8019
                                                 else ());
                                                (let uu____8024 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____8024))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____8033 =
                                                 let uu____8038 = mk_lid name
                                                    in
                                                 let uu____8039 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____8038 uu____8039
                                                  in
                                               (match uu____8033 with
                                                | (sigelt,fv) ->
                                                    ((let uu____8043 =
                                                        let uu____8046 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____8046
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____8043);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____8100 =
                                             let uu____8103 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____8106 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____8103 :: uu____8106  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____8100);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____8158 =
                                              let uu____8161 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____8162 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____8161 :: uu____8162  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____8158);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____8214 =
                                               let uu____8217 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____8220 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____8217 :: uu____8220  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____8214);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____8272 =
                                                let uu____8275 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____8276 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____8275 :: uu____8276  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____8272);
                                             (let uu____8325 =
                                                FStar_List.fold_left
                                                  (fun uu____8365  ->
                                                     fun action  ->
                                                       match uu____8365 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____8386 =
                                                             let uu____8393 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____8393
                                                               params_un
                                                              in
                                                           (match uu____8386
                                                            with
                                                            | (action_params,env',uu____8402)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____8428
                                                                     ->
                                                                    match uu____8428
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____8447
                                                                    =
                                                                    let uu___965_8448
                                                                    = bv  in
                                                                    let uu____8449
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___965_8448.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___965_8448.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____8449
                                                                    }  in
                                                                    (uu____8447,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____8455
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____8455
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
                                                                    uu____8494
                                                                    ->
                                                                    let uu____8495
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____8495
                                                                     in
                                                                    ((
                                                                    let uu____8499
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____8499
                                                                    then
                                                                    let uu____8504
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____8507
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____8510
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____8512
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____8504
                                                                    uu____8507
                                                                    uu____8510
                                                                    uu____8512
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
                                                                    let uu____8521
                                                                    =
                                                                    let uu____8524
                                                                    =
                                                                    let uu___987_8525
                                                                    = action
                                                                     in
                                                                    let uu____8526
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____8527
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___987_8525.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___987_8525.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___987_8525.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____8526;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____8527
                                                                    }  in
                                                                    uu____8524
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____8521))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____8325 with
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
                                                      let uu____8571 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____8578 =
                                                        let uu____8587 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____8587]  in
                                                      uu____8571 ::
                                                        uu____8578
                                                       in
                                                    let uu____8612 =
                                                      let uu____8615 =
                                                        let uu____8616 =
                                                          let uu____8617 =
                                                            let uu____8634 =
                                                              let uu____8645
                                                                =
                                                                let uu____8654
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____8657
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____8654,
                                                                  uu____8657)
                                                                 in
                                                              [uu____8645]
                                                               in
                                                            (repr,
                                                              uu____8634)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____8617
                                                           in
                                                        mk1 uu____8616  in
                                                      let uu____8693 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____8615
                                                        uu____8693
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____8612
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____8694 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____8698 =
                                                    let uu____8707 =
                                                      let uu____8708 =
                                                        let uu____8711 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____8711
                                                         in
                                                      uu____8708.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____8707 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____8725)
                                                        ->
                                                        let uu____8762 =
                                                          let uu____8783 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____8783
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____8851 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____8762
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____8916 =
                                                               let uu____8917
                                                                 =
                                                                 let uu____8920
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____8920
                                                                  in
                                                               uu____8917.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____8916
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____8953
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____8953
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____8968
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____8999
                                                                     ->
                                                                    match uu____8999
                                                                    with
                                                                    | 
                                                                    (bv,uu____9008)
                                                                    ->
                                                                    let uu____9013
                                                                    =
                                                                    let uu____9015
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____9015
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____9013
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____8968
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
                                                                    let uu____9107
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____9107
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____9117
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____9128
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____9128
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____9138
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____9141
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____9138,
                                                                    uu____9141)))
                                                              | uu____9156 ->
                                                                  let uu____9157
                                                                    =
                                                                    let uu____9163
                                                                    =
                                                                    let uu____9165
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____9165
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____9163)
                                                                     in
                                                                  raise_error1
                                                                    uu____9157))
                                                    | uu____9177 ->
                                                        let uu____9178 =
                                                          let uu____9184 =
                                                            let uu____9186 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____9186
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____9184)
                                                           in
                                                        raise_error1
                                                          uu____9178
                                                     in
                                                  (match uu____8698 with
                                                   | (pre,post) ->
                                                       ((let uu____9219 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____9222 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____9225 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___1043_9228
                                                             = ed  in
                                                           let uu____9229 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____9230 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____9231 =
                                                             let uu____9232 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____9232)
                                                              in
                                                           let uu____9239 =
                                                             let uu____9240 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____9240)
                                                              in
                                                           let uu____9247 =
                                                             apply_close
                                                               repr2
                                                              in
                                                           let uu____9248 =
                                                             let uu____9249 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____9249)
                                                              in
                                                           let uu____9256 =
                                                             let uu____9257 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____9257)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.is_layered
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.is_layered);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____9229;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____9230;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____9231;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____9239;
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.match_wps
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.match_wps);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____9247;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____9248;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____9256;
                                                             FStar_Syntax_Syntax.stronger_repr
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.stronger_repr);
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___1043_9228.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____9264 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____9264
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____9282
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____9282
                                                               then
                                                                 let uu____9286
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____9286
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
                                                                    let uu____9306
                                                                    =
                                                                    let uu____9309
                                                                    =
                                                                    let uu____9310
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____9310)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____9309
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
                                                                    uu____9306;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____9317
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____9317
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____9320
                                                                 =
                                                                 let uu____9323
                                                                   =
                                                                   let uu____9326
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____9326
                                                                    in
                                                                 FStar_List.append
                                                                   uu____9323
                                                                   sigelts'
                                                                  in
                                                               (uu____9320,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_lex_t :
  'Auu____9367 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____9367 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____9402 = FStar_List.hd ses  in
            uu____9402.FStar_Syntax_Syntax.sigrng  in
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
           | uu____9407 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____9413,[],t,uu____9415,uu____9416);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____9418;
               FStar_Syntax_Syntax.sigattrs = uu____9419;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____9421,_t_top,_lex_t_top,_9455,uu____9424);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____9426;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____9427;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____9429,_t_cons,_lex_t_cons,_9463,uu____9432);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____9434;
                 FStar_Syntax_Syntax.sigattrs = uu____9435;_}::[]
               when
               ((_9455 = Prims.int_zero) && (_9463 = Prims.int_zero)) &&
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
                 let uu____9488 =
                   let uu____9495 =
                     let uu____9496 =
                       let uu____9503 =
                         let uu____9506 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____9506
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____9503, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____9496  in
                   FStar_Syntax_Syntax.mk uu____9495  in
                 uu____9488 FStar_Pervasives_Native.None r1  in
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
                   let uu____9521 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____9521
                    in
                 let hd1 =
                   let uu____9523 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____9523
                    in
                 let tl1 =
                   let uu____9525 =
                     let uu____9526 =
                       let uu____9533 =
                         let uu____9534 =
                           let uu____9541 =
                             let uu____9544 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____9544
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____9541, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____9534  in
                       FStar_Syntax_Syntax.mk uu____9533  in
                     uu____9526 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____9525
                    in
                 let res =
                   let uu____9550 =
                     let uu____9557 =
                       let uu____9558 =
                         let uu____9565 =
                           let uu____9568 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____9568
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____9565,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____9558  in
                     FStar_Syntax_Syntax.mk uu____9557  in
                   uu____9550 FStar_Pervasives_Native.None r2  in
                 let uu____9571 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____9571
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
               let uu____9610 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____9610;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____9615 ->
               let err_msg =
                 let uu____9620 =
                   let uu____9622 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____9622  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____9620
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
    fun uu____9647  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____9647 with
          | (uvs,t) ->
              let uu____9660 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____9660 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____9672 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____9672 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____9690 =
                        let uu____9693 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____9693
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____9690)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____9716 =
          let uu____9717 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____9717 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____9716 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____9742 =
          let uu____9743 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____9743 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____9742 r
  
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
          (let uu____9792 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____9792
           then
             let uu____9795 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____9795
           else ());
          (let uu____9800 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____9800 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____9831 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____9831 FStar_List.flatten  in
               ((let uu____9845 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____9848 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____9848)
                    in
                 if uu____9845
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
                           let uu____9864 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____9874,uu____9875,uu____9876,uu____9877,uu____9878)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____9887 -> failwith "Impossible!"  in
                           match uu____9864 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Inductive type "
                                      (Prims.op_Hat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____9906 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____9916,uu____9917,ty_lid,uu____9919,uu____9920)
                               -> (data_lid, ty_lid)
                           | uu____9927 -> failwith "Impossible"  in
                         match uu____9906 with
                         | (data_lid,ty_lid) ->
                             let uu____9935 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____9938 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____9938)
                                in
                             if uu____9935
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.op_Hat "Exception "
                                      (Prims.op_Hat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____9952 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____9957,uu____9958,uu____9959,uu____9960,uu____9961)
                         -> lid
                     | uu____9970 -> failwith "Impossible"  in
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
                   let uu____9988 =
                     (((FStar_List.length tcs) = Prims.int_zero) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____9988
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
          let pop1 uu____10063 =
            let uu____10064 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___1221_10074  ->
               match () with
               | () ->
                   let uu____10081 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____10081 (fun r  -> pop1 (); r))
              ()
          with
          | uu___1220_10112 -> (pop1 (); FStar_Exn.raise uu___1220_10112)
  
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
      | uu____10428 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____10486 = FStar_ToSyntax_ToSyntax.get_fail_attr true at
              in
           comb uu____10486 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____10511 .
    'Auu____10511 FStar_Pervasives_Native.option -> 'Auu____10511 Prims.list
  =
  fun uu___0_10520  ->
    match uu___0_10520 with
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
            let uu____10600 = collect1 tl1  in
            (match uu____10600 with
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
        | ((e,n1)::uu____10838,[]) ->
            FStar_Pervasives_Native.Some (e, n1, Prims.int_zero)
        | ([],(e,n1)::uu____10894) ->
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
          let uu____11104 =
            let uu____11106 = FStar_Options.ide ()  in
            Prims.op_Negation uu____11106  in
          if uu____11104
          then
            let uu____11109 =
              let uu____11114 = FStar_TypeChecker_Env.dsenv env  in
              let uu____11115 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____11114 uu____11115  in
            (match uu____11109 with
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
                              let uu____11148 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____11149 =
                                let uu____11155 =
                                  let uu____11157 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____11159 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____11157 uu____11159
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____11155)
                                 in
                              FStar_Errors.log_issue uu____11148 uu____11149
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____11166 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____11167 =
                                   let uu____11173 =
                                     let uu____11175 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____11175
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____11173)
                                    in
                                 FStar_Errors.log_issue uu____11166
                                   uu____11167)
                              else ())
                         else ())))
          else ()
      | uu____11185 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____11230 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____11258 ->
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
             let uu____11318 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11318
             then
               let ses1 =
                 let uu____11326 =
                   let uu____11327 =
                     let uu____11328 =
                       tc_inductive
                         (let uu___1353_11337 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___1353_11337.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___1353_11337.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___1353_11337.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___1353_11337.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___1353_11337.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___1353_11337.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___1353_11337.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___1353_11337.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___1353_11337.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___1353_11337.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___1353_11337.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___1353_11337.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___1353_11337.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___1353_11337.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___1353_11337.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___1353_11337.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___1353_11337.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___1353_11337.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___1353_11337.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___1353_11337.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___1353_11337.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___1353_11337.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___1353_11337.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___1353_11337.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___1353_11337.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___1353_11337.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___1353_11337.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___1353_11337.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___1353_11337.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___1353_11337.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___1353_11337.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___1353_11337.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___1353_11337.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___1353_11337.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___1353_11337.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___1353_11337.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___1353_11337.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___1353_11337.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___1353_11337.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___1353_11337.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___1353_11337.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___1353_11337.FStar_TypeChecker_Env.strict_args_tab)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____11328
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____11327
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____11326
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____11351 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____11351
                 then
                   let uu____11356 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___1357_11360 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1357_11360.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1357_11360.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1357_11360.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1357_11360.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____11356
                 else ());
                ses1)
             else ses  in
           let uu____11370 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____11370 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___1364_11394 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1364_11394.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1364_11394.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___1364_11394.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1364_11394.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ne ->
           let uu____11406 = cps_and_elaborate env ne  in
           (match uu____11406 with
            | (ses,ne1,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | FStar_Pervasives_Native.Some lift ->
                      [(let uu___1378_11445 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1378_11445.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1378_11445.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1378_11445.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1378_11445.FStar_Syntax_Syntax.sigattrs)
                        });
                      lift]
                  | FStar_Pervasives_Native.None  ->
                      [(let uu___1381_11447 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_new_effect ne1);
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1381_11447.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1381_11447.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1381_11447.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1381_11447.FStar_Syntax_Syntax.sigattrs)
                        })]
                   in
                ([], (FStar_List.append ses effect_and_lift_ses), env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____11454 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____11454
             then
               let uu____11459 = FStar_Syntax_Print.sigelt_to_string se  in
               FStar_Util.print1
                 "Starting to typecheck layered effect:\n%s\n" uu____11459
             else ());
            (let tc_fun =
               if ne.FStar_Syntax_Syntax.is_layered
               then tc_layered_eff_decl
               else tc_eff_decl  in
             let ne1 =
               let uu____11483 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env)
                  in
               if uu____11483
               then
                 let ne1 =
                   let uu____11487 =
                     let uu____11488 =
                       let uu____11489 =
                         tc_fun
                           (let uu___1391_11492 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1391_11492.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1391_11492.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1391_11492.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1391_11492.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1391_11492.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1391_11492.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1391_11492.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1391_11492.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1391_11492.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1391_11492.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1391_11492.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1391_11492.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1391_11492.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1391_11492.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1391_11492.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1391_11492.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1391_11492.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1391_11492.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1391_11492.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1391_11492.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1391_11492.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___1391_11492.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1391_11492.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1391_11492.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1391_11492.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1391_11492.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1391_11492.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1391_11492.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1391_11492.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1391_11492.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1391_11492.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1391_11492.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1391_11492.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1391_11492.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1391_11492.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1391_11492.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1391_11492.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1391_11492.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1391_11492.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1391_11492.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1391_11492.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1391_11492.FStar_TypeChecker_Env.strict_args_tab)
                            }) ne
                          in
                       FStar_All.pipe_right uu____11489
                         (fun ne1  ->
                            let uu___1394_11498 = se  in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_new_effect ne1);
                              FStar_Syntax_Syntax.sigrng =
                                (uu___1394_11498.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___1394_11498.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___1394_11498.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___1394_11498.FStar_Syntax_Syntax.sigattrs)
                            })
                        in
                     FStar_All.pipe_right uu____11488
                       (FStar_TypeChecker_Normalize.elim_uvars env)
                      in
                   FStar_All.pipe_right uu____11487
                     FStar_Syntax_Util.eff_decl_of_new_effect
                    in
                 ((let uu____11500 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "TwoPhases")
                      in
                   if uu____11500
                   then
                     let uu____11505 =
                       FStar_Syntax_Print.sigelt_to_string
                         (let uu___1398_11509 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne1);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1398_11509.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1398_11509.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1398_11509.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1398_11509.FStar_Syntax_Syntax.sigattrs)
                          })
                        in
                     FStar_Util.print1 "Effect decl after phase 1: %s\n"
                       uu____11505
                   else ());
                  ne1)
               else ne  in
             let ne2 = tc_fun env ne1  in
             let se1 =
               let uu___1403_11517 = se  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1403_11517.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1403_11517.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1403_11517.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1403_11517.FStar_Syntax_Syntax.sigattrs)
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
           let uu____11525 =
             let uu____11532 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____11532
              in
           (match uu____11525 with
            | (a,wp_a_src) ->
                let uu____11549 =
                  let uu____11556 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____11556
                   in
                (match uu____11549 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____11574 =
                         let uu____11577 =
                           let uu____11578 =
                             let uu____11585 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____11585)  in
                           FStar_Syntax_Syntax.NT uu____11578  in
                         [uu____11577]  in
                       FStar_Syntax_Subst.subst uu____11574 wp_b_tgt  in
                     let expected_k =
                       let uu____11593 =
                         let uu____11602 = FStar_Syntax_Syntax.mk_binder a
                            in
                         let uu____11609 =
                           let uu____11618 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____11618]  in
                         uu____11602 :: uu____11609  in
                       let uu____11643 =
                         FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                       FStar_Syntax_Util.arrow uu____11593 uu____11643  in
                     let repr_type eff_name a1 wp =
                       (let uu____11665 =
                          let uu____11667 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____11667  in
                        if uu____11665
                        then
                          let uu____11670 =
                            let uu____11676 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____11676)
                             in
                          let uu____11680 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____11670 uu____11680
                        else ());
                       (let uu____11683 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____11683 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([], (ed.FStar_Syntax_Syntax.repr))
                               in
                            let uu____11720 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____11721 =
                              let uu____11728 =
                                let uu____11729 =
                                  let uu____11746 =
                                    let uu____11757 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____11766 =
                                      let uu____11777 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____11777]  in
                                    uu____11757 :: uu____11766  in
                                  (repr, uu____11746)  in
                                FStar_Syntax_Syntax.Tm_app uu____11729  in
                              FStar_Syntax_Syntax.mk uu____11728  in
                            uu____11721 FStar_Pervasives_Native.None
                              uu____11720)
                        in
                     let uu____11822 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____11995 =
                             if (FStar_List.length uvs) > Prims.int_zero
                             then
                               let uu____12006 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____12006 with
                               | (usubst,uvs1) ->
                                   let uu____12029 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____12030 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____12029, uu____12030)
                             else (env, lift_wp)  in
                           (match uu____11995 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if (FStar_List.length uvs) = Prims.int_zero
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____12080 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____12080))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____12151 =
                             if (FStar_List.length what) > Prims.int_zero
                             then
                               let uu____12166 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____12166 with
                               | (usubst,uvs) ->
                                   let uu____12191 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____12191)
                             else ([], lift)  in
                           (match uu____12151 with
                            | (uvs,lift1) ->
                                ((let uu____12227 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____12227
                                  then
                                    let uu____12231 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____12231
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____12237 =
                                    let uu____12244 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____12244 lift1
                                     in
                                  match uu____12237 with
                                  | (lift2,comp,uu____12269) ->
                                      let uu____12270 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____12270 with
                                       | (uu____12299,lift_wp,lift_elab) ->
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
                                             let uu____12331 =
                                               let uu____12342 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____12342
                                                in
                                             let uu____12359 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____12331, uu____12359)
                                           else
                                             (let uu____12388 =
                                                let uu____12399 =
                                                  let uu____12408 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____12408)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____12399
                                                 in
                                              let uu____12423 =
                                                let uu____12432 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____12432)  in
                                              (uu____12388, uu____12423))))))
                        in
                     (match uu____11822 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___1479_12506 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___1479_12506.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___1479_12506.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___1479_12506.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___1479_12506.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___1479_12506.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___1479_12506.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___1479_12506.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___1479_12506.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___1479_12506.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___1479_12506.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___1479_12506.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___1479_12506.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___1479_12506.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___1479_12506.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___1479_12506.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___1479_12506.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___1479_12506.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___1479_12506.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___1479_12506.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___1479_12506.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___1479_12506.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___1479_12506.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___1479_12506.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___1479_12506.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___1479_12506.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___1479_12506.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___1479_12506.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___1479_12506.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___1479_12506.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___1479_12506.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___1479_12506.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___1479_12506.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___1479_12506.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___1479_12506.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___1479_12506.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___1479_12506.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___1479_12506.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___1479_12506.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___1479_12506.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___1479_12506.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___1479_12506.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___1479_12506.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___1479_12506.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____12563 =
                                  let uu____12568 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____12568 with
                                  | (usubst,uvs1) ->
                                      let uu____12591 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____12592 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____12591, uu____12592)
                                   in
                                (match uu____12563 with
                                 | (env2,lift2) ->
                                     let uu____12605 =
                                       let uu____12612 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____12612
                                        in
                                     (match uu____12605 with
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
                                              let uu____12646 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____12647 =
                                                let uu____12654 =
                                                  let uu____12655 =
                                                    let uu____12672 =
                                                      let uu____12683 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____12692 =
                                                        let uu____12703 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____12703]  in
                                                      uu____12683 ::
                                                        uu____12692
                                                       in
                                                    (lift_wp1, uu____12672)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____12655
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____12654
                                                 in
                                              uu____12647
                                                FStar_Pervasives_Native.None
                                                uu____12646
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____12751 =
                                              let uu____12760 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____12767 =
                                                let uu____12776 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____12783 =
                                                  let uu____12792 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____12792]  in
                                                uu____12776 :: uu____12783
                                                 in
                                              uu____12760 :: uu____12767  in
                                            let uu____12823 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____12751 uu____12823
                                             in
                                          let uu____12826 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____12826 with
                                           | (expected_k2,uu____12844,uu____12845)
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
                                                    let uu____12869 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____12869))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____12885 =
                              let uu____12887 =
                                let uu____12889 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____12889
                                  FStar_List.length
                                 in
                              uu____12887 <> Prims.int_one  in
                            if uu____12885
                            then
                              let uu____12911 =
                                let uu____12917 =
                                  let uu____12919 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____12921 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____12923 =
                                    let uu____12925 =
                                      let uu____12927 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____12927
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____12925
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____12919 uu____12921 uu____12923
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____12917)
                                 in
                              FStar_Errors.raise_error uu____12911 r
                            else ());
                           (let uu____12954 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____12965 =
                                   let uu____12967 =
                                     let uu____12970 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____12970
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____12967
                                     FStar_List.length
                                    in
                                 uu____12965 <> Prims.int_one)
                               in
                            if uu____12954
                            then
                              let uu____13024 =
                                let uu____13030 =
                                  let uu____13032 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____13034 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____13036 =
                                    let uu____13038 =
                                      let uu____13040 =
                                        let uu____13043 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____13043
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____13040
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____13038
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____13032 uu____13034 uu____13036
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____13030)
                                 in
                              FStar_Errors.raise_error uu____13024 r
                            else ());
                           (let sub2 =
                              let uu___1516_13102 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___1516_13102.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___1516_13102.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___1519_13104 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___1519_13104.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___1519_13104.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___1519_13104.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___1519_13104.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags) ->
           let uu____13118 =
             if (FStar_List.length uvs) = Prims.int_zero
             then (env, uvs, tps, c)
             else
               (let uu____13146 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____13146 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____13177 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____13177 c  in
                    let uu____13186 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____13186, uvs1, tps1, c1))
              in
           (match uu____13118 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____13208 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____13208 with
                 | (tps2,c2) ->
                     let uu____13225 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____13225 with
                      | (tps3,env3,us) ->
                          let uu____13245 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____13245 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____13273)::uu____13274 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____13293 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____13301 =
                                   let uu____13303 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____13303  in
                                 if uu____13301
                                 then
                                   let uu____13306 =
                                     let uu____13312 =
                                       let uu____13314 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____13316 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____13314 uu____13316
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____13312)
                                      in
                                   FStar_Errors.raise_error uu____13306 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____13324 =
                                   let uu____13325 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____13325
                                    in
                                 match uu____13324 with
                                 | (uvs2,t) ->
                                     let uu____13356 =
                                       let uu____13361 =
                                         let uu____13374 =
                                           let uu____13375 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____13375.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____13374)  in
                                       match uu____13361 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____13390,c5)) -> ([], c5)
                                       | (uu____13432,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____13471 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____13356 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               Prims.int_one
                                           then
                                             (let uu____13505 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____13505 with
                                              | (uu____13510,t1) ->
                                                  let uu____13512 =
                                                    let uu____13518 =
                                                      let uu____13520 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____13522 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____13526 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____13520
                                                        uu____13522
                                                        uu____13526
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____13518)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____13512 r)
                                           else ();
                                           (let se1 =
                                              let uu___1589_13533 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___1589_13533.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___1589_13533.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___1589_13533.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___1589_13533.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13540,uu____13541,uu____13542) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_13547  ->
                   match uu___1_13547 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13550 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____13556,uu____13557) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___1_13566  ->
                   match uu___1_13566 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13569 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____13580 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____13580
             then
               let uu____13583 =
                 let uu____13589 =
                   let uu____13591 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____13591
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____13589)
                  in
               FStar_Errors.raise_error uu____13583 r
             else ());
            (let uu____13597 =
               let uu____13606 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____13606
               then
                 let uu____13617 =
                   tc_declare_typ
                     (let uu___1613_13620 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1613_13620.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1613_13620.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1613_13620.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1613_13620.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1613_13620.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1613_13620.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1613_13620.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1613_13620.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1613_13620.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1613_13620.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1613_13620.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1613_13620.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1613_13620.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1613_13620.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1613_13620.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1613_13620.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1613_13620.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1613_13620.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1613_13620.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1613_13620.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1613_13620.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1613_13620.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1613_13620.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1613_13620.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1613_13620.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1613_13620.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1613_13620.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1613_13620.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1613_13620.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1613_13620.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1613_13620.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1613_13620.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1613_13620.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1613_13620.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1613_13620.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1613_13620.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1613_13620.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1613_13620.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1613_13620.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1613_13620.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___1613_13620.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___1613_13620.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1613_13620.FStar_TypeChecker_Env.strict_args_tab)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____13617 with
                 | (uvs1,t1) ->
                     ((let uu____13645 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____13645
                       then
                         let uu____13650 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____13652 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____13650 uu____13652
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____13597 with
             | (uvs1,t1) ->
                 let uu____13687 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____13687 with
                  | (uvs2,t2) ->
                      ([(let uu___1626_13717 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1626_13717.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1626_13717.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1626_13717.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1626_13717.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____13722 =
             let uu____13731 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____13731
             then
               let uu____13742 =
                 tc_assume
                   (let uu___1635_13745 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1635_13745.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1635_13745.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1635_13745.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1635_13745.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1635_13745.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1635_13745.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1635_13745.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1635_13745.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1635_13745.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1635_13745.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___1635_13745.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1635_13745.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1635_13745.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1635_13745.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1635_13745.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1635_13745.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1635_13745.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1635_13745.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1635_13745.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1635_13745.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1635_13745.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___1635_13745.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1635_13745.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1635_13745.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1635_13745.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1635_13745.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1635_13745.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1635_13745.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1635_13745.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1635_13745.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1635_13745.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1635_13745.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1635_13745.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1635_13745.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1635_13745.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1635_13745.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___1635_13745.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1635_13745.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1635_13745.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1635_13745.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1635_13745.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1635_13745.FStar_TypeChecker_Env.strict_args_tab)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____13742 with
               | (uvs1,t1) ->
                   ((let uu____13771 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____13771
                     then
                       let uu____13776 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____13778 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____13776
                         uu____13778
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____13722 with
            | (uvs1,t1) ->
                let uu____13813 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____13813 with
                 | (uvs2,t2) ->
                     ([(let uu___1648_13843 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___1648_13843.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___1648_13843.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___1648_13843.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___1648_13843.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____13847 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____13847 with
            | (e1,c,g1) ->
                let uu____13867 =
                  let uu____13874 =
                    let uu____13877 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____13877  in
                  let uu____13878 =
                    let uu____13883 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____13883)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____13874 uu____13878
                   in
                (match uu____13867 with
                 | (e2,uu____13895,g) ->
                     ((let uu____13898 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____13898);
                      (let se1 =
                         let uu___1663_13900 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___1663_13900.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___1663_13900.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___1663_13900.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___1663_13900.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____13912 = FStar_Options.debug_any ()  in
             if uu____13912
             then
               let uu____13915 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____13917 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____13915
                 uu____13917
             else ());
            (let uu____13922 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____13922 with
             | (t1,uu____13940,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____13954 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____13954 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____13957 =
                              let uu____13963 =
                                let uu____13965 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____13967 =
                                  let uu____13969 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____13969
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____13965 uu____13967
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____13963)
                               in
                            FStar_Errors.raise_error uu____13957 r
                        | uu____13981 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___1684_13986 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___1684_13986.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___1684_13986.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___1684_13986.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___1684_13986.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___1684_13986.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___1684_13986.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___1684_13986.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___1684_13986.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___1684_13986.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___1684_13986.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___1684_13986.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___1684_13986.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___1684_13986.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___1684_13986.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___1684_13986.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___1684_13986.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___1684_13986.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___1684_13986.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___1684_13986.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___1684_13986.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___1684_13986.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___1684_13986.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___1684_13986.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___1684_13986.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___1684_13986.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___1684_13986.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___1684_13986.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___1684_13986.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___1684_13986.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___1684_13986.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___1684_13986.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___1684_13986.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___1684_13986.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___1684_13986.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___1684_13986.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___1684_13986.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___1684_13986.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___1684_13986.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___1684_13986.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___1684_13986.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___1684_13986.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___1684_13986.FStar_TypeChecker_Env.nbe);
                        FStar_TypeChecker_Env.strict_args_tab =
                          (uu___1684_13986.FStar_TypeChecker_Env.strict_args_tab)
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
                 let uu____14054 =
                   let uu____14056 =
                     let uu____14065 = drop_logic val_q  in
                     let uu____14068 = drop_logic q'  in
                     (uu____14065, uu____14068)  in
                   match uu____14056 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____14054
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____14095 =
                      let uu____14101 =
                        let uu____14103 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____14105 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____14107 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____14103 uu____14105 uu____14107
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____14101)
                       in
                    FStar_Errors.raise_error uu____14095 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____14144 =
                   let uu____14145 = FStar_Syntax_Subst.compress def  in
                   uu____14145.FStar_Syntax_Syntax.n  in
                 match uu____14144 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____14157,uu____14158) -> binders
                 | uu____14183 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____14195;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____14300) -> val_bs1
                     | (uu____14331,[]) -> val_bs1
                     | ((body_bv,uu____14363)::bt,(val_bv,aqual)::vt) ->
                         let uu____14420 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____14444) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___1753_14458 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___1755_14461 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___1755_14461.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___1753_14458.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1753_14458.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____14420
                      in
                   let uu____14468 =
                     let uu____14475 =
                       let uu____14476 =
                         let uu____14491 = rename_binders1 def_bs val_bs  in
                         (uu____14491, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14476  in
                     FStar_Syntax_Syntax.mk uu____14475  in
                   uu____14468 FStar_Pervasives_Native.None r1
               | uu____14510 -> typ1  in
             let uu___1761_14511 = lb  in
             let uu____14512 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___1761_14511.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___1761_14511.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____14512;
               FStar_Syntax_Syntax.lbeff =
                 (uu___1761_14511.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___1761_14511.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___1761_14511.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___1761_14511.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____14515 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____14570  ->
                     fun lb  ->
                       match uu____14570 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____14616 =
                             let uu____14628 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____14628 with
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
                                   | uu____14708 ->
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
                                  (let uu____14755 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____14755, quals_opt1)))
                              in
                           (match uu____14616 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____14515 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____14859 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___2_14865  ->
                                match uu___2_14865 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____14870 -> false))
                         in
                      if uu____14859
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____14883 =
                    let uu____14890 =
                      let uu____14891 =
                        let uu____14905 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____14905)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____14891  in
                    FStar_Syntax_Syntax.mk uu____14890  in
                  uu____14883 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___1804_14924 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___1804_14924.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___1804_14924.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___1804_14924.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___1804_14924.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___1804_14924.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___1804_14924.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___1804_14924.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___1804_14924.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___1804_14924.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___1804_14924.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___1804_14924.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___1804_14924.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___1804_14924.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___1804_14924.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___1804_14924.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___1804_14924.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___1804_14924.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___1804_14924.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___1804_14924.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___1804_14924.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___1804_14924.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___1804_14924.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___1804_14924.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___1804_14924.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___1804_14924.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___1804_14924.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___1804_14924.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___1804_14924.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___1804_14924.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___1804_14924.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___1804_14924.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___1804_14924.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___1804_14924.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___1804_14924.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___1804_14924.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___1804_14924.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___1804_14924.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___1804_14924.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___1804_14924.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___1804_14924.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___1804_14924.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___1804_14924.FStar_TypeChecker_Env.strict_args_tab)
                  }  in
                let e1 =
                  let uu____14927 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____14927
                  then
                    let drop_lbtyp e_lax =
                      let uu____14936 =
                        let uu____14937 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____14937.FStar_Syntax_Syntax.n  in
                      match uu____14936 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____14959 =
                              let uu____14960 = FStar_Syntax_Subst.compress e
                                 in
                              uu____14960.FStar_Syntax_Syntax.n  in
                            match uu____14959 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____14964,lb1::[]),uu____14966) ->
                                let uu____14982 =
                                  let uu____14983 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____14983.FStar_Syntax_Syntax.n  in
                                (match uu____14982 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____14988 -> false)
                            | uu____14990 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___1829_14994 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___1831_15009 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___1831_15009.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___1831_15009.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___1831_15009.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___1831_15009.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___1831_15009.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___1831_15009.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___1829_14994.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___1829_14994.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____15012 -> e_lax  in
                    let uu____15013 =
                      FStar_Util.record_time
                        (fun uu____15021  ->
                           let uu____15022 =
                             let uu____15023 =
                               let uu____15024 =
                                 FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                   (let uu___1835_15033 = env'  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1835_15033.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1835_15033.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1835_15033.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1835_15033.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1835_15033.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1835_15033.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1835_15033.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1835_15033.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1835_15033.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1835_15033.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___1835_15033.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1835_15033.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1835_15033.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1835_15033.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1835_15033.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1835_15033.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1835_15033.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1835_15033.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1835_15033.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1835_15033.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1835_15033.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1835_15033.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1835_15033.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1835_15033.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1835_15033.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1835_15033.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1835_15033.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1835_15033.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1835_15033.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1835_15033.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1835_15033.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1835_15033.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1835_15033.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1835_15033.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1835_15033.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1835_15033.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1835_15033.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1835_15033.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1835_15033.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1835_15033.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1835_15033.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1835_15033.FStar_TypeChecker_Env.strict_args_tab)
                                    }) e
                                  in
                               FStar_All.pipe_right uu____15024
                                 (fun uu____15046  ->
                                    match uu____15046 with
                                    | (e1,uu____15054,uu____15055) -> e1)
                                in
                             FStar_All.pipe_right uu____15023
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env')
                              in
                           FStar_All.pipe_right uu____15022 drop_lbtyp)
                       in
                    match uu____15013 with
                    | (e1,ms) ->
                        ((let uu____15061 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TwoPhases")
                             in
                          if uu____15061
                          then
                            let uu____15066 =
                              FStar_Syntax_Print.term_to_string e1  in
                            FStar_Util.print1
                              "Let binding after phase 1: %s\n" uu____15066
                          else ());
                         (let uu____15072 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "TCDeclTime")
                             in
                          if uu____15072
                          then
                            let uu____15077 = FStar_Util.string_of_int ms  in
                            FStar_Util.print1
                              "Let binding elaborated (phase 1) in %s milliseconds\n"
                              uu____15077
                          else ());
                         e1)
                  else e  in
                let uu____15084 =
                  let uu____15093 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____15093 with
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
                (match uu____15084 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___1865_15198 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___1865_15198.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1865_15198.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1865_15198.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1865_15198.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___1872_15211 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1872_15211.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1872_15211.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___1872_15211.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___1872_15211.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1872_15211.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1872_15211.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____15212 =
                       FStar_Util.record_time
                         (fun uu____15231  ->
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              env' e1)
                        in
                     (match uu____15212 with
                      | (r1,ms) ->
                          ((let uu____15259 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TCDeclTime")
                               in
                            if uu____15259
                            then
                              let uu____15264 = FStar_Util.string_of_int ms
                                 in
                              FStar_Util.print1
                                "Let binding typechecked in phase 2 in %s milliseconds\n"
                                uu____15264
                            else ());
                           (let uu____15269 =
                              match r1 with
                              | ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                                   FStar_Syntax_Syntax.pos = uu____15294;
                                   FStar_Syntax_Syntax.vars = uu____15295;_},uu____15296,g)
                                  when FStar_TypeChecker_Env.is_trivial g ->
                                  let lbs2 =
                                    let uu____15326 =
                                      FStar_All.pipe_right
                                        (FStar_Pervasives_Native.snd lbs1)
                                        (FStar_List.map rename_parameters)
                                       in
                                    ((FStar_Pervasives_Native.fst lbs1),
                                      uu____15326)
                                     in
                                  let lbs3 =
                                    let uu____15350 =
                                      match post_tau with
                                      | FStar_Pervasives_Native.Some tau ->
                                          FStar_List.map (postprocess_lb tau)
                                            (FStar_Pervasives_Native.snd lbs2)
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.snd lbs2
                                       in
                                    ((FStar_Pervasives_Native.fst lbs2),
                                      uu____15350)
                                     in
                                  let quals1 =
                                    match e2.FStar_Syntax_Syntax.n with
                                    | FStar_Syntax_Syntax.Tm_meta
                                        (uu____15373,FStar_Syntax_Syntax.Meta_desugared
                                         (FStar_Syntax_Syntax.Masked_effect
                                         ))
                                        ->
                                        FStar_Syntax_Syntax.HasMaskedEffect
                                        :: quals
                                    | uu____15378 -> quals  in
                                  ((let uu___1902_15387 = se1  in
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           (lbs3, lids));
                                      FStar_Syntax_Syntax.sigrng =
                                        (uu___1902_15387.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (uu___1902_15387.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (uu___1902_15387.FStar_Syntax_Syntax.sigattrs)
                                    }), lbs3)
                              | uu____15390 ->
                                  failwith
                                    "impossible (typechecking should preserve Tm_let)"
                               in
                            match uu____15269 with
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
                                 (let uu____15446 = log env1  in
                                  if uu____15446
                                  then
                                    let uu____15449 =
                                      let uu____15451 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_List.map
                                             (fun lb  ->
                                                let should_log =
                                                  let uu____15471 =
                                                    let uu____15480 =
                                                      let uu____15481 =
                                                        let uu____15484 =
                                                          FStar_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname
                                                           in
                                                        uu____15484.FStar_Syntax_Syntax.fv_name
                                                         in
                                                      uu____15481.FStar_Syntax_Syntax.v
                                                       in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu____15480
                                                     in
                                                  match uu____15471 with
                                                  | FStar_Pervasives_Native.None
                                                       -> true
                                                  | uu____15493 -> false  in
                                                if should_log
                                                then
                                                  let uu____15505 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  let uu____15507 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp
                                                     in
                                                  FStar_Util.format2
                                                    "let %s : %s" uu____15505
                                                    uu____15507
                                                else ""))
                                         in
                                      FStar_All.pipe_right uu____15451
                                        (FStar_String.concat "\n")
                                       in
                                    FStar_Util.print1 "%s\n" uu____15449
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
      (let uu____15559 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____15559
       then
         let uu____15562 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____15562
       else ());
      (let uu____15567 = get_fail_se se  in
       match uu____15567 with
       | FStar_Pervasives_Native.Some (uu____15588,false ) when
           let uu____15605 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____15605 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___1933_15631 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___1933_15631.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___1933_15631.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___1933_15631.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___1933_15631.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___1933_15631.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___1933_15631.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___1933_15631.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___1933_15631.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___1933_15631.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___1933_15631.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___1933_15631.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___1933_15631.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___1933_15631.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___1933_15631.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___1933_15631.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___1933_15631.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___1933_15631.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___1933_15631.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___1933_15631.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___1933_15631.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___1933_15631.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___1933_15631.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___1933_15631.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___1933_15631.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___1933_15631.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___1933_15631.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___1933_15631.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___1933_15631.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___1933_15631.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___1933_15631.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___1933_15631.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___1933_15631.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___1933_15631.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___1933_15631.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___1933_15631.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___1933_15631.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___1933_15631.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___1933_15631.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___1933_15631.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___1933_15631.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___1933_15631.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___1933_15631.FStar_TypeChecker_Env.nbe);
                 FStar_TypeChecker_Env.strict_args_tab =
                   (uu___1933_15631.FStar_TypeChecker_Env.strict_args_tab)
               }
             else env1  in
           ((let uu____15636 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____15636
             then
               let uu____15639 =
                 let uu____15641 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____15641
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____15639
             else ());
            (let uu____15655 =
               FStar_Errors.catch_errors
                 (fun uu____15685  ->
                    FStar_Options.with_saved_options
                      (fun uu____15697  -> tc_decl' env' se))
                in
             match uu____15655 with
             | (errs,uu____15709) ->
                 ((let uu____15739 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____15739
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____15774 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____15774  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____15786 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____15797 =
                            let uu____15807 = check_multi_eq errnos1 actual
                               in
                            match uu____15807 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- Prims.int_one), (~- Prims.int_one),
                                  (~- Prims.int_one))
                             in
                          (match uu____15797 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____15872 =
                                   let uu____15878 =
                                     let uu____15880 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____15883 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____15886 =
                                       FStar_Util.string_of_int e  in
                                     let uu____15888 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____15890 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____15880 uu____15883 uu____15886
                                       uu____15888 uu____15890
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____15878)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15872)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____15917 .
    'Auu____15917 ->
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
               (fun uu___3_15960  ->
                  match uu___3_15960 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____15963 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____15974) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____15982 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____15992 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____15997 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____16013 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____16039 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16065) ->
            let uu____16074 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____16074
            then
              let for_export_bundle se1 uu____16111 =
                match uu____16111 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____16150,uu____16151) ->
                         let dec =
                           let uu___2009_16161 = se1  in
                           let uu____16162 =
                             let uu____16163 =
                               let uu____16170 =
                                 let uu____16171 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____16171  in
                               (l, us, uu____16170)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____16163
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____16162;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___2009_16161.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___2009_16161.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___2009_16161.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____16181,uu____16182,uu____16183) ->
                         let dec =
                           let uu___2020_16191 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___2020_16191.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___2020_16191.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___2020_16191.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____16196 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____16219,uu____16220,uu____16221) ->
            let uu____16222 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____16222 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____16246 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____16246
            then
              ([(let uu___2036_16265 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___2036_16265.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___2036_16265.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___2036_16265.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____16268 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___4_16274  ->
                         match uu___4_16274 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____16277 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____16283 ->
                             true
                         | uu____16285 -> false))
                  in
               if uu____16268 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____16306 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____16311 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16316 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____16321 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____16326 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____16344) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____16358 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____16358
            then ([], hidden)
            else
              (let dec =
                 let uu____16379 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____16379;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____16390 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____16390
            then
              let uu____16401 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___2073_16415 = se  in
                        let uu____16416 =
                          let uu____16417 =
                            let uu____16424 =
                              let uu____16425 =
                                let uu____16428 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____16428.FStar_Syntax_Syntax.fv_name  in
                              uu____16425.FStar_Syntax_Syntax.v  in
                            (uu____16424, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____16417  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____16416;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___2073_16415.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___2073_16415.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___2073_16415.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____16401, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____16451 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____16451
       then
         let uu____16454 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____16454
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____16459 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____16477 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
           uu____16494) ->
           let env1 =
             let uu___2094_16499 = env  in
             let uu____16500 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2094_16499.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2094_16499.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2094_16499.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2094_16499.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2094_16499.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2094_16499.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2094_16499.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2094_16499.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2094_16499.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2094_16499.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2094_16499.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2094_16499.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2094_16499.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2094_16499.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2094_16499.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2094_16499.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2094_16499.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2094_16499.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2094_16499.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2094_16499.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2094_16499.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2094_16499.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2094_16499.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2094_16499.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2094_16499.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2094_16499.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2094_16499.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2094_16499.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2094_16499.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2094_16499.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2094_16499.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2094_16499.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2094_16499.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2094_16499.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16500;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2094_16499.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2094_16499.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2094_16499.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2094_16499.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2094_16499.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2094_16499.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2094_16499.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2094_16499.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2094_16499.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
           let env1 =
             let uu___2094_16502 = env  in
             let uu____16503 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2094_16502.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2094_16502.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2094_16502.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2094_16502.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2094_16502.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2094_16502.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2094_16502.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2094_16502.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2094_16502.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2094_16502.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2094_16502.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2094_16502.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2094_16502.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2094_16502.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2094_16502.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2094_16502.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2094_16502.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2094_16502.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2094_16502.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2094_16502.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2094_16502.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2094_16502.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2094_16502.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2094_16502.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2094_16502.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2094_16502.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2094_16502.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2094_16502.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2094_16502.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2094_16502.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2094_16502.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2094_16502.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2094_16502.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2094_16502.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16503;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2094_16502.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2094_16502.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2094_16502.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2094_16502.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2094_16502.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2094_16502.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2094_16502.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2094_16502.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2094_16502.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions
           uu____16504) ->
           let env1 =
             let uu___2094_16507 = env  in
             let uu____16508 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2094_16507.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2094_16507.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2094_16507.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2094_16507.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2094_16507.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2094_16507.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2094_16507.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2094_16507.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2094_16507.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2094_16507.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2094_16507.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2094_16507.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2094_16507.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2094_16507.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2094_16507.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2094_16507.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2094_16507.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2094_16507.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2094_16507.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2094_16507.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2094_16507.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2094_16507.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2094_16507.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2094_16507.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2094_16507.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2094_16507.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2094_16507.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2094_16507.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2094_16507.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2094_16507.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2094_16507.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2094_16507.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2094_16507.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2094_16507.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16508;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2094_16507.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2094_16507.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2094_16507.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2094_16507.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2094_16507.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2094_16507.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2094_16507.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2094_16507.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2094_16507.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____16509) ->
           let env1 =
             let uu___2094_16514 = env  in
             let uu____16515 = FStar_Options.using_facts_from ()  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2094_16514.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2094_16514.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2094_16514.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2094_16514.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2094_16514.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2094_16514.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2094_16514.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2094_16514.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2094_16514.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2094_16514.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2094_16514.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2094_16514.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2094_16514.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2094_16514.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2094_16514.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2094_16514.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2094_16514.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___2094_16514.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___2094_16514.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2094_16514.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2094_16514.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2094_16514.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2094_16514.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2094_16514.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2094_16514.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2094_16514.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2094_16514.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2094_16514.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2094_16514.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2094_16514.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2094_16514.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2094_16514.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2094_16514.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2094_16514.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns = uu____16515;
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2094_16514.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2094_16514.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2094_16514.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2094_16514.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2094_16514.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2094_16514.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2094_16514.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2094_16514.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2094_16514.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           env1
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
           ->
           ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
              ();
            env)
       | FStar_Syntax_Syntax.Sig_pragma uu____16517 -> env
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____16518 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____16528 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____16528) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____16529,uu____16530,uu____16531) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_16536  ->
                   match uu___5_16536 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____16539 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____16541,uu____16542) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___5_16551  ->
                   match uu___5_16551 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____16554 -> false))
           -> env
       | uu____16556 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____16625 se =
        match uu____16625 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____16678 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____16678
              then
                let uu____16681 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____16681
              else ());
             (let uu____16686 = tc_decl env1 se  in
              match uu____16686 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____16739 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____16739
                             then
                               let uu____16743 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____16743
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____16759 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____16759
                             then
                               let uu____16763 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____16763
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
                    (let uu____16780 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____16780
                     then
                       let uu____16785 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____16794 =
                                  let uu____16796 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.op_Hat uu____16796 "\n"  in
                                Prims.op_Hat s uu____16794) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____16785
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____16806 =
                       let uu____16815 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____16815
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____16857 se1 =
                            match uu____16857 with
                            | (exports1,hidden1) ->
                                let uu____16885 = for_export env3 hidden1 se1
                                   in
                                (match uu____16885 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____16806 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____17039 = acc  in
        match uu____17039 with
        | (uu____17074,uu____17075,env1,uu____17077) ->
            let uu____17090 =
              FStar_Util.record_time
                (fun uu____17137  -> process_one_decl acc se)
               in
            (match uu____17090 with
             | (r,ms_elapsed) ->
                 ((let uu____17203 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____17203
                   then
                     let uu____17207 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____17209 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____17207 uu____17209
                   else ());
                  r))
         in
      let uu____17214 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____17214 with
      | (ses1,exports,env1,uu____17262) ->
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
          let uu___2191_17300 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___2191_17300.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___2191_17300.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___2191_17300.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___2191_17300.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___2191_17300.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___2191_17300.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___2191_17300.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___2191_17300.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___2191_17300.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___2191_17300.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___2191_17300.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___2191_17300.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___2191_17300.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___2191_17300.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___2191_17300.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___2191_17300.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___2191_17300.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___2191_17300.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___2191_17300.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___2191_17300.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___2191_17300.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___2191_17300.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___2191_17300.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___2191_17300.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___2191_17300.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___2191_17300.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___2191_17300.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___2191_17300.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___2191_17300.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___2191_17300.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___2191_17300.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___2191_17300.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___2191_17300.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___2191_17300.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___2191_17300.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___2191_17300.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___2191_17300.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___2191_17300.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___2191_17300.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___2191_17300.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___2191_17300.FStar_TypeChecker_Env.strict_args_tab)
          }  in
        let check_term lid univs1 t =
          let uu____17320 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____17320 with
          | (univs2,t1) ->
              ((let uu____17328 =
                  let uu____17330 =
                    let uu____17336 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____17336  in
                  FStar_All.pipe_left uu____17330
                    (FStar_Options.Other "Exports")
                   in
                if uu____17328
                then
                  let uu____17340 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____17342 =
                    let uu____17344 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____17344
                      (FStar_String.concat ", ")
                     in
                  let uu____17361 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____17340 uu____17342 uu____17361
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____17367 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____17367 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____17393 =
             let uu____17395 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____17397 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____17395 uu____17397
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____17393);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17408) ->
              let uu____17417 =
                let uu____17419 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17419  in
              if uu____17417
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____17433,uu____17434) ->
              let t =
                let uu____17446 =
                  let uu____17453 =
                    let uu____17454 =
                      let uu____17469 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____17469)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____17454  in
                  FStar_Syntax_Syntax.mk uu____17453  in
                uu____17446 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____17485,uu____17486,uu____17487) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____17497 =
                let uu____17499 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17499  in
              if uu____17497 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____17507,lbs),uu____17509) ->
              let uu____17520 =
                let uu____17522 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17522  in
              if uu____17520
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
              let uu____17545 =
                let uu____17547 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____17547  in
              if uu____17545
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____17568 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____17569 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____17576 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____17577 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____17578 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____17579 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____17586 -> ()  in
        let uu____17587 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17587 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____17693) -> true
             | uu____17695 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____17725 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____17764 ->
                   let uu____17765 =
                     let uu____17772 =
                       let uu____17773 =
                         let uu____17788 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____17788)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____17773  in
                     FStar_Syntax_Syntax.mk uu____17772  in
                   uu____17765 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____17805,uu____17806) ->
            let s1 =
              let uu___2317_17816 = s  in
              let uu____17817 =
                let uu____17818 =
                  let uu____17825 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____17825)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____17818  in
              let uu____17826 =
                let uu____17829 =
                  let uu____17832 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____17832  in
                FStar_Syntax_Syntax.Assumption :: uu____17829  in
              {
                FStar_Syntax_Syntax.sigel = uu____17817;
                FStar_Syntax_Syntax.sigrng =
                  (uu___2317_17816.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____17826;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2317_17816.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___2317_17816.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____17835 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____17860 lbdef =
        match uu____17860 with
        | (uvs,t) ->
            let attrs =
              let uu____17871 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____17871
              then
                let uu____17876 =
                  let uu____17877 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____17877
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____17876 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___2330_17880 = s  in
            let uu____17881 =
              let uu____17884 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____17884  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___2330_17880.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____17881;
              FStar_Syntax_Syntax.sigmeta =
                (uu___2330_17880.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____17902 -> failwith "Impossible!"  in
        let c_opt =
          let uu____17909 = FStar_Syntax_Util.is_unit t  in
          if uu____17909
          then
            let uu____17916 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____17916
          else
            (let uu____17923 =
               let uu____17924 = FStar_Syntax_Subst.compress t  in
               uu____17924.FStar_Syntax_Syntax.n  in
             match uu____17923 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____17931,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____17955 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____17967 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____17967
            then false
            else
              (let uu____17974 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____17974
               then true
               else
                 (let uu____17981 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____17981))
         in
      let extract_sigelt s =
        (let uu____17993 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____17993
         then
           let uu____17996 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____17996
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____18003 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____18023 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____18042 ->
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
                             (lid,uu____18088,uu____18089,uu____18090,uu____18091,uu____18092)
                             ->
                             ((let uu____18102 =
                                 let uu____18105 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____18105  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____18102);
                              (let uu____18154 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____18154 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____18158,uu____18159,uu____18160,uu____18161,uu____18162)
                             ->
                             ((let uu____18170 =
                                 let uu____18173 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____18173  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____18170);
                              sigelts1)
                         | uu____18222 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____18231 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____18231
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____18241 =
                    let uu___2394_18242 = s  in
                    let uu____18243 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2394_18242.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2394_18242.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____18243;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2394_18242.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2394_18242.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____18241])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____18254 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____18254
             then []
             else
               (let uu____18261 = lbs  in
                match uu____18261 with
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
                        (fun uu____18323  ->
                           match uu____18323 with
                           | (uu____18331,t,uu____18333) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____18350  ->
                             match uu____18350 with
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
                           (fun uu____18377  ->
                              match uu____18377 with
                              | (uu____18385,t,uu____18387) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____18399,uu____18400) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____18408 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____18437 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____18437) uu____18408
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____18441 =
                    let uu___2436_18442 = s  in
                    let uu____18443 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___2436_18442.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___2436_18442.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____18443;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___2436_18442.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___2436_18442.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____18441]
                else [])
             else
               (let uu____18450 =
                  let uu___2438_18451 = s  in
                  let uu____18452 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___2438_18451.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___2438_18451.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____18452;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___2438_18451.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___2438_18451.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____18450])
         | FStar_Syntax_Syntax.Sig_new_effect uu____18455 -> [s]
         | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18456 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____18457 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18458 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____18471 -> [s])
         in
      let uu___2450_18472 = m  in
      let uu____18473 =
        let uu____18474 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____18474 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___2450_18472.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____18473;
        FStar_Syntax_Syntax.exports =
          (uu___2450_18472.FStar_Syntax_Syntax.exports);
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
        (fun uu____18525  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____18572  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____18587 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____18587
  
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
      (let uu____18676 = FStar_Options.debug_any ()  in
       if uu____18676
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
         let uu___2475_18692 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___2475_18692.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___2475_18692.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___2475_18692.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___2475_18692.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___2475_18692.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___2475_18692.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___2475_18692.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___2475_18692.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___2475_18692.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___2475_18692.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___2475_18692.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___2475_18692.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___2475_18692.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___2475_18692.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___2475_18692.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___2475_18692.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___2475_18692.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___2475_18692.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___2475_18692.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___2475_18692.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___2475_18692.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___2475_18692.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___2475_18692.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___2475_18692.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___2475_18692.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___2475_18692.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___2475_18692.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___2475_18692.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___2475_18692.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___2475_18692.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___2475_18692.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___2475_18692.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___2475_18692.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___2475_18692.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___2475_18692.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___2475_18692.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___2475_18692.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___2475_18692.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___2475_18692.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___2475_18692.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___2475_18692.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___2475_18692.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____18694 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____18694 with
       | (ses,exports,env3) ->
           ((let uu___2483_18727 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___2483_18727.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___2483_18727.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___2483_18727.FStar_Syntax_Syntax.is_interface)
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
        let uu____18756 = tc_decls env decls  in
        match uu____18756 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___2492_18787 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___2492_18787.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___2492_18787.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___2492_18787.FStar_Syntax_Syntax.is_interface)
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
        let uu____18848 = tc_partial_modul env01 m  in
        match uu____18848 with
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
                (let uu____18885 = FStar_Errors.get_err_count ()  in
                 uu____18885 = Prims.int_zero)
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____18896 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____18896
                then
                  let uu____18900 =
                    let uu____18902 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____18902 then "" else " (in lax mode) "  in
                  let uu____18910 =
                    let uu____18912 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____18912
                    then
                      let uu____18916 =
                        let uu____18918 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.op_Hat uu____18918 "\n"  in
                      Prims.op_Hat "\nfrom: " uu____18916
                    else ""  in
                  let uu____18925 =
                    let uu____18927 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____18927
                    then
                      let uu____18931 =
                        let uu____18933 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.op_Hat uu____18933 "\n"  in
                      Prims.op_Hat "\nto: " uu____18931
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____18900
                    uu____18910 uu____18925
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.op_Hat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___2518_18947 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2518_18947.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2518_18947.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2518_18947.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2518_18947.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2518_18947.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2518_18947.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2518_18947.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2518_18947.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2518_18947.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2518_18947.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2518_18947.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2518_18947.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2518_18947.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2518_18947.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2518_18947.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2518_18947.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2518_18947.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2518_18947.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2518_18947.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2518_18947.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2518_18947.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2518_18947.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2518_18947.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2518_18947.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2518_18947.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2518_18947.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2518_18947.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2518_18947.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2518_18947.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2518_18947.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2518_18947.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___2518_18947.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2518_18947.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2518_18947.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2518_18947.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2518_18947.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2518_18947.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2518_18947.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2518_18947.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2518_18947.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2518_18947.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2518_18947.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2518_18947.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let en02 =
                    let uu___2521_18949 = en01  in
                    let uu____18950 =
                      let uu____18965 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____18965, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___2521_18949.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___2521_18949.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___2521_18949.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___2521_18949.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___2521_18949.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___2521_18949.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___2521_18949.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___2521_18949.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___2521_18949.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___2521_18949.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___2521_18949.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___2521_18949.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___2521_18949.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___2521_18949.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___2521_18949.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___2521_18949.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___2521_18949.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___2521_18949.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___2521_18949.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___2521_18949.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___2521_18949.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___2521_18949.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___2521_18949.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___2521_18949.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___2521_18949.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___2521_18949.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___2521_18949.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___2521_18949.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___2521_18949.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___2521_18949.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___2521_18949.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____18950;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___2521_18949.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___2521_18949.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___2521_18949.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___2521_18949.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___2521_18949.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___2521_18949.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___2521_18949.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___2521_18949.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___2521_18949.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___2521_18949.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___2521_18949.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___2521_18949.FStar_TypeChecker_Env.strict_args_tab)
                    }  in
                  let uu____19011 =
                    let uu____19013 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____19013  in
                  if uu____19011
                  then
                    ((let uu____19017 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____19017 (fun a3  -> ()));
                     en02)
                  else en02  in
                let uu____19021 = tc_modul en0 modul_iface true  in
                match uu____19021 with
                | (modul_iface1,env) ->
                    ((let uu___2530_19034 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___2530_19034.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___2530_19034.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___2530_19034.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___2532_19038 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___2532_19038.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___2532_19038.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___2532_19038.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____19041 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____19041 FStar_Util.smap_clear);
               (let uu____19077 =
                  ((let uu____19081 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____19081) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____19084 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____19084)
                   in
                if uu____19077 then check_exports env modul exports else ());
               (let uu____19090 =
                  pop_context env
                    (Prims.op_Hat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____19090 (fun a4  -> ()));
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
        let uu____19105 =
          let uu____19107 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.op_Hat "Internals for " uu____19107  in
        push_context env uu____19105  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____19128 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____19139 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____19139 with | (uu____19146,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____19171 = FStar_Options.debug_any ()  in
         if uu____19171
         then
           let uu____19174 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____19174
         else ());
        (let uu____19186 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____19186
         then
           let uu____19189 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____19189
         else ());
        (let env1 =
           let uu___2562_19195 = env  in
           let uu____19196 =
             let uu____19198 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____19198  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2562_19195.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2562_19195.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2562_19195.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2562_19195.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2562_19195.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2562_19195.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2562_19195.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2562_19195.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2562_19195.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2562_19195.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___2562_19195.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2562_19195.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2562_19195.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2562_19195.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2562_19195.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2562_19195.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2562_19195.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2562_19195.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___2562_19195.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2562_19195.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____19196;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2562_19195.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2562_19195.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2562_19195.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2562_19195.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2562_19195.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2562_19195.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2562_19195.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___2562_19195.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2562_19195.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2562_19195.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2562_19195.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2562_19195.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2562_19195.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2562_19195.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2562_19195.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2562_19195.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___2562_19195.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___2562_19195.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2562_19195.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2562_19195.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2562_19195.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___2562_19195.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2562_19195.FStar_TypeChecker_Env.strict_args_tab)
           }  in
         let uu____19200 = tc_modul env1 m b  in
         match uu____19200 with
         | (m1,env2) ->
             ((let uu____19212 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____19212
               then
                 let uu____19215 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____19215
               else ());
              (let uu____19221 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____19221
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
                         let uu____19259 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____19259 with
                         | (univnames1,e) ->
                             let uu___2584_19266 = lb  in
                             let uu____19267 =
                               let uu____19270 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____19270 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2584_19266.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2584_19266.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___2584_19266.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2584_19266.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____19267;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2584_19266.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2584_19266.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___2586_19271 = se  in
                       let uu____19272 =
                         let uu____19273 =
                           let uu____19280 =
                             let uu____19281 = FStar_List.map update lbs  in
                             (b1, uu____19281)  in
                           (uu____19280, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____19273  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____19272;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___2586_19271.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___2586_19271.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___2586_19271.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___2586_19271.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____19289 -> se  in
                 let normalized_module =
                   let uu___2590_19291 = m1  in
                   let uu____19292 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___2590_19291.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____19292;
                     FStar_Syntax_Syntax.exports =
                       (uu___2590_19291.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___2590_19291.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____19293 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____19293
               else ());
              (m1, env2)))
  