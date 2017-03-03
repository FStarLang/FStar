open Prims
let set_hint_correlator:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for () in
      match uu____7 with
      | Some l ->
          let lid =
            let _0_244 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix _0_244 l in
          let uu___83_11 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___83_11.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___83_11.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___83_11.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___83_11.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___83_11.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___83_11.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___83_11.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___83_11.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___83_11.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___83_11.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___83_11.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___83_11.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___83_11.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___83_11.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___83_11.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___83_11.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___83_11.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___83_11.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___83_11.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___83_11.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___83_11.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___83_11.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___83_11.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let _0_247 = FStar_TypeChecker_Env.current_module env in
                let _0_246 =
                  let _0_245 = FStar_Syntax_Syntax.next_id () in
                  FStar_All.pipe_right _0_245 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix _0_247 _0_246
            | l::uu____18 -> l in
          let uu___84_20 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___84_20.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___84_20.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___84_20.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___84_20.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___84_20.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___84_20.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___84_20.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___84_20.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___84_20.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___84_20.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___84_20.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___84_20.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___84_20.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___84_20.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___84_20.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___84_20.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___84_20.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___84_20.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___84_20.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___84_20.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___84_20.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___84_20.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___84_20.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
let log: FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (Prims.op_Negation
         (let _0_248 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_248))
let tc_check_trivial_guard:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____35 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k in
        match uu____35 with
        | (t,c,g) ->
            (FStar_ST.write t.FStar_Syntax_Syntax.tk
               (Some ((c.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t)
let recheck_debug:
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____57 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
         if uu____57
         then
           let _0_249 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s _0_249
         else ());
        (let uu____59 = FStar_TypeChecker_TcTerm.tc_term env t in
         match uu____59 with
         | (t',uu____64,uu____65) ->
             ((let uu____67 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
               if uu____67
               then
                 let _0_250 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   _0_250
               else ());
              t))
let check_and_gen:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let _0_251 = tc_check_trivial_guard env t k in
        FStar_TypeChecker_Util.generalize_universes env _0_251
let check_nogen env t k =
  let t = tc_check_trivial_guard env t k in
  let _0_252 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t in
  ([], _0_252)
let monad_signature:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv*
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____120 =
          Prims.raise
            (FStar_Errors.Error
               (let _0_253 =
                  FStar_TypeChecker_Err.unexpected_signature_for_monad env m
                    s in
                (_0_253, (FStar_Ident.range_of_lid m)))) in
        let s = FStar_Syntax_Subst.compress s in
        match s.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs = FStar_Syntax_Subst.open_binders bs in
            (match bs with
             | (a,uu____148)::(wp,uu____150)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____159 -> fail ())
        | uu____160 -> fail ()
let rec tc_eff_decl:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____223 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____223 with
      | (effect_params_un,signature_un,opening) ->
          let uu____230 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un in
          (match uu____230 with
           | (effect_params,env,uu____236) ->
               let uu____237 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____237 with
                | (signature,uu____241) ->
                    let ed =
                      let uu___85_243 = ed in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___85_243.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___85_243.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___85_243.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___85_243.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___85_243.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___85_243.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___85_243.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___85_243.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___85_243.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___85_243.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___85_243.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___85_243.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___85_243.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___85_243.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___85_243.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___85_243.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___85_243.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___85_243.FStar_Syntax_Syntax.actions)
                      } in
                    let ed =
                      match effect_params with
                      | [] -> ed
                      | uu____247 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts) in
                            ([], t1) in
                          let uu___86_265 = ed in
                          let _0_269 = op ed.FStar_Syntax_Syntax.ret_wp in
                          let _0_268 = op ed.FStar_Syntax_Syntax.bind_wp in
                          let _0_267 = op ed.FStar_Syntax_Syntax.if_then_else in
                          let _0_266 = op ed.FStar_Syntax_Syntax.ite_wp in
                          let _0_265 = op ed.FStar_Syntax_Syntax.stronger in
                          let _0_264 = op ed.FStar_Syntax_Syntax.close_wp in
                          let _0_263 = op ed.FStar_Syntax_Syntax.assert_p in
                          let _0_262 = op ed.FStar_Syntax_Syntax.assume_p in
                          let _0_261 = op ed.FStar_Syntax_Syntax.null_wp in
                          let _0_260 = op ed.FStar_Syntax_Syntax.trivial in
                          let _0_259 =
                            Prims.snd
                              (op ([], (ed.FStar_Syntax_Syntax.repr))) in
                          let _0_258 = op ed.FStar_Syntax_Syntax.return_repr in
                          let _0_257 = op ed.FStar_Syntax_Syntax.bind_repr in
                          let _0_256 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___87_269 = a in
                                 let _0_255 =
                                   Prims.snd
                                     (op
                                        ([],
                                          (a.FStar_Syntax_Syntax.action_defn))) in
                                 let _0_254 =
                                   Prims.snd
                                     (op
                                        ([],
                                          (a.FStar_Syntax_Syntax.action_typ))) in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___87_269.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___87_269.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___87_269.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn = _0_255;
                                   FStar_Syntax_Syntax.action_typ = _0_254
                                 }) ed.FStar_Syntax_Syntax.actions in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___86_265.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___86_265.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___86_265.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___86_265.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___86_265.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___86_265.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = _0_269;
                            FStar_Syntax_Syntax.bind_wp = _0_268;
                            FStar_Syntax_Syntax.if_then_else = _0_267;
                            FStar_Syntax_Syntax.ite_wp = _0_266;
                            FStar_Syntax_Syntax.stronger = _0_265;
                            FStar_Syntax_Syntax.close_wp = _0_264;
                            FStar_Syntax_Syntax.assert_p = _0_263;
                            FStar_Syntax_Syntax.assume_p = _0_262;
                            FStar_Syntax_Syntax.null_wp = _0_261;
                            FStar_Syntax_Syntax.trivial = _0_260;
                            FStar_Syntax_Syntax.repr = _0_259;
                            FStar_Syntax_Syntax.return_repr = _0_258;
                            FStar_Syntax_Syntax.bind_repr = _0_257;
                            FStar_Syntax_Syntax.actions = _0_256
                          } in
                    let wp_with_fresh_result_type env mname signature =
                      let fail t =
                        Prims.raise
                          (FStar_Errors.Error
                             (let _0_270 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env mname t in
                              (_0_270, (FStar_Ident.range_of_lid mname)))) in
                      let uu____300 =
                        (FStar_Syntax_Subst.compress signature).FStar_Syntax_Syntax.n in
                      match uu____300 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs = FStar_Syntax_Subst.open_binders bs in
                          (match bs with
                           | (a,uu____323)::(wp,uu____325)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____334 -> fail signature)
                      | uu____335 -> fail signature in
                    let uu____336 =
                      wp_with_fresh_result_type env
                        ed.FStar_Syntax_Syntax.mname
                        ed.FStar_Syntax_Syntax.signature in
                    (match uu____336 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____354 =
                           let uu____355 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un in
                           match uu____355 with
                           | (signature,uu____363) ->
                               wp_with_fresh_result_type env
                                 ed.FStar_Syntax_Syntax.mname signature in
                         let env =
                           let _0_271 =
                             FStar_Syntax_Syntax.new_bv None
                               ed.FStar_Syntax_Syntax.signature in
                           FStar_TypeChecker_Env.push_bv env _0_271 in
                         ((let uu____366 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____366
                           then
                             let _0_276 =
                               FStar_Syntax_Print.lid_to_string
                                 ed.FStar_Syntax_Syntax.mname in
                             let _0_275 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed.FStar_Syntax_Syntax.binders in
                             let _0_274 =
                               FStar_Syntax_Print.term_to_string
                                 ed.FStar_Syntax_Syntax.signature in
                             let _0_273 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Syntax.bv_to_name a) in
                             let _0_272 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               _0_276 _0_275 _0_274 _0_273 _0_272
                           else ());
                          (let check_and_gen' env uu____379 k =
                             match uu____379 with
                             | (uu____384,t) -> check_and_gen env t k in
                           let return_wp =
                             let expected_k =
                               let _0_281 =
                                 let _0_279 = FStar_Syntax_Syntax.mk_binder a in
                                 let _0_278 =
                                   let _0_277 =
                                     FStar_Syntax_Syntax.null_binder
                                       (FStar_Syntax_Syntax.bv_to_name a) in
                                   [_0_277] in
                                 _0_279 :: _0_278 in
                               let _0_280 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a in
                               FStar_Syntax_Util.arrow _0_281 _0_280 in
                             check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp
                               expected_k in
                           let bind_wp =
                             let uu____393 = fresh_effect_signature () in
                             match uu____393 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let _0_284 =
                                     let _0_282 =
                                       FStar_Syntax_Syntax.null_binder
                                         (FStar_Syntax_Syntax.bv_to_name a) in
                                     [_0_282] in
                                   let _0_283 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow _0_284 _0_283 in
                                 let expected_k =
                                   let _0_295 =
                                     let _0_293 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range in
                                     let _0_292 =
                                       let _0_291 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let _0_290 =
                                         let _0_289 =
                                           FStar_Syntax_Syntax.mk_binder b in
                                         let _0_288 =
                                           let _0_287 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a in
                                           let _0_286 =
                                             let _0_285 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b in
                                             [_0_285] in
                                           _0_287 :: _0_286 in
                                         _0_289 :: _0_288 in
                                       _0_291 :: _0_290 in
                                     _0_293 :: _0_292 in
                                   let _0_294 =
                                     FStar_Syntax_Syntax.mk_Total wp_b in
                                   FStar_Syntax_Util.arrow _0_295 _0_294 in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.bind_wp expected_k in
                           let if_then_else =
                             let p =
                               let _0_297 =
                                 let _0_296 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right _0_296 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname)) _0_297 in
                             let expected_k =
                               let _0_306 =
                                 let _0_304 = FStar_Syntax_Syntax.mk_binder a in
                                 let _0_303 =
                                   let _0_302 =
                                     FStar_Syntax_Syntax.mk_binder p in
                                   let _0_301 =
                                     let _0_300 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     let _0_299 =
                                       let _0_298 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [_0_298] in
                                     _0_300 :: _0_299 in
                                   _0_302 :: _0_301 in
                                 _0_304 :: _0_303 in
                               let _0_305 = FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow _0_306 _0_305 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.if_then_else expected_k in
                           let ite_wp =
                             let expected_k =
                               let _0_311 =
                                 let _0_309 = FStar_Syntax_Syntax.mk_binder a in
                                 let _0_308 =
                                   let _0_307 =
                                     FStar_Syntax_Syntax.null_binder wp_a in
                                   [_0_307] in
                                 _0_309 :: _0_308 in
                               let _0_310 = FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow _0_311 _0_310 in
                             check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp
                               expected_k in
                           let stronger =
                             let uu____422 = FStar_Syntax_Util.type_u () in
                             match uu____422 with
                             | (t,uu____426) ->
                                 let expected_k =
                                   let _0_318 =
                                     let _0_316 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let _0_315 =
                                       let _0_314 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       let _0_313 =
                                         let _0_312 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a in
                                         [_0_312] in
                                       _0_314 :: _0_313 in
                                     _0_316 :: _0_315 in
                                   let _0_317 =
                                     FStar_Syntax_Syntax.mk_Total t in
                                   FStar_Syntax_Util.arrow _0_318 _0_317 in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.stronger expected_k in
                           let close_wp =
                             let b =
                               let _0_320 =
                                 let _0_319 = FStar_Syntax_Util.type_u () in
                                 FStar_All.pipe_right _0_319 Prims.fst in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname)) _0_320 in
                             let b_wp_a =
                               let _0_323 =
                                 let _0_321 =
                                   FStar_Syntax_Syntax.null_binder
                                     (FStar_Syntax_Syntax.bv_to_name b) in
                                 [_0_321] in
                               let _0_322 = FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow _0_323 _0_322 in
                             let expected_k =
                               let _0_330 =
                                 let _0_328 = FStar_Syntax_Syntax.mk_binder a in
                                 let _0_327 =
                                   let _0_326 =
                                     FStar_Syntax_Syntax.mk_binder b in
                                   let _0_325 =
                                     let _0_324 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a in
                                     [_0_324] in
                                   _0_326 :: _0_325 in
                                 _0_328 :: _0_327 in
                               let _0_329 = FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow _0_330 _0_329 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.close_wp expected_k in
                           let assert_p =
                             let expected_k =
                               let _0_338 =
                                 let _0_336 = FStar_Syntax_Syntax.mk_binder a in
                                 let _0_335 =
                                   let _0_334 =
                                     FStar_Syntax_Syntax.null_binder
                                       (let _0_331 =
                                          FStar_Syntax_Util.type_u () in
                                        FStar_All.pipe_right _0_331 Prims.fst) in
                                   let _0_333 =
                                     let _0_332 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [_0_332] in
                                   _0_334 :: _0_333 in
                                 _0_336 :: _0_335 in
                               let _0_337 = FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow _0_338 _0_337 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assert_p expected_k in
                           let assume_p =
                             let expected_k =
                               let _0_346 =
                                 let _0_344 = FStar_Syntax_Syntax.mk_binder a in
                                 let _0_343 =
                                   let _0_342 =
                                     FStar_Syntax_Syntax.null_binder
                                       (let _0_339 =
                                          FStar_Syntax_Util.type_u () in
                                        FStar_All.pipe_right _0_339 Prims.fst) in
                                   let _0_341 =
                                     let _0_340 =
                                       FStar_Syntax_Syntax.null_binder wp_a in
                                     [_0_340] in
                                   _0_342 :: _0_341 in
                                 _0_344 :: _0_343 in
                               let _0_345 = FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow _0_346 _0_345 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assume_p expected_k in
                           let null_wp =
                             let expected_k =
                               let _0_349 =
                                 let _0_347 = FStar_Syntax_Syntax.mk_binder a in
                                 [_0_347] in
                               let _0_348 = FStar_Syntax_Syntax.mk_Total wp_a in
                               FStar_Syntax_Util.arrow _0_349 _0_348 in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.null_wp expected_k in
                           let trivial_wp =
                             let uu____457 = FStar_Syntax_Util.type_u () in
                             match uu____457 with
                             | (t,uu____461) ->
                                 let expected_k =
                                   let _0_354 =
                                     let _0_352 =
                                       FStar_Syntax_Syntax.mk_binder a in
                                     let _0_351 =
                                       let _0_350 =
                                         FStar_Syntax_Syntax.null_binder wp_a in
                                       [_0_350] in
                                     _0_352 :: _0_351 in
                                   let _0_353 =
                                     FStar_Syntax_Syntax.mk_GTotal t in
                                   FStar_Syntax_Util.arrow _0_354 _0_353 in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.trivial expected_k in
                           let uu____465 =
                             let uu____471 =
                               (FStar_Syntax_Subst.compress
                                  ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n in
                             match uu____471 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed.FStar_Syntax_Syntax.repr),
                                   (ed.FStar_Syntax_Syntax.bind_repr),
                                   (ed.FStar_Syntax_Syntax.return_repr),
                                   (ed.FStar_Syntax_Syntax.actions))
                             | uu____478 ->
                                 let repr =
                                   let uu____480 =
                                     FStar_Syntax_Util.type_u () in
                                   match uu____480 with
                                   | (t,uu____484) ->
                                       let expected_k =
                                         let _0_359 =
                                           let _0_357 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let _0_356 =
                                             let _0_355 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a in
                                             [_0_355] in
                                           _0_357 :: _0_356 in
                                         let _0_358 =
                                           FStar_Syntax_Syntax.mk_GTotal t in
                                         FStar_Syntax_Util.arrow _0_359
                                           _0_358 in
                                       tc_check_trivial_guard env
                                         ed.FStar_Syntax_Syntax.repr
                                         expected_k in
                                 let mk_repr' t wp =
                                   let repr =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env repr in
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (let _0_363 =
                                            let _0_362 =
                                              FStar_Syntax_Syntax.as_arg t in
                                            let _0_361 =
                                              let _0_360 =
                                                FStar_Syntax_Syntax.as_arg wp in
                                              [_0_360] in
                                            _0_362 :: _0_361 in
                                          (repr, _0_363)))) None
                                     FStar_Range.dummyRange in
                                 let mk_repr a wp =
                                   let _0_364 =
                                     FStar_Syntax_Syntax.bv_to_name a in
                                   mk_repr' _0_364 wp in
                                 let destruct_repr t =
                                   let uu____526 =
                                     (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
                                   match uu____526 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____533,(t,uu____535)::(wp,uu____537)::[])
                                       -> (t, wp)
                                   | uu____571 ->
                                       failwith "Unexpected repr type" in
                                 let bind_repr =
                                   let r =
                                     let _0_365 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None in
                                     FStar_All.pipe_right _0_365
                                       FStar_Syntax_Syntax.fv_to_tm in
                                   let uu____580 = fresh_effect_signature () in
                                   match uu____580 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let _0_368 =
                                           let _0_366 =
                                             FStar_Syntax_Syntax.null_binder
                                               (FStar_Syntax_Syntax.bv_to_name
                                                  a) in
                                           [_0_366] in
                                         let _0_367 =
                                           FStar_Syntax_Syntax.mk_Total wp_b in
                                         FStar_Syntax_Util.arrow _0_368
                                           _0_367 in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b in
                                       let x_a =
                                         let _0_369 =
                                           FStar_Syntax_Syntax.bv_to_name a in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None _0_369 in
                                       let wp_g_x =
                                         (let _0_373 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              wp_g in
                                          let _0_372 =
                                            let _0_371 =
                                              let _0_370 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x_a in
                                              FStar_All.pipe_left
                                                FStar_Syntax_Syntax.as_arg
                                                _0_370 in
                                            [_0_371] in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            _0_373 _0_372) None
                                           FStar_Range.dummyRange in
                                       let res =
                                         let wp =
                                           (let _0_385 =
                                              let _0_374 =
                                                FStar_TypeChecker_Env.inst_tscheme
                                                  bind_wp in
                                              FStar_All.pipe_right _0_374
                                                Prims.snd in
                                            let _0_384 =
                                              let _0_383 =
                                                let _0_382 =
                                                  let _0_381 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  let _0_380 =
                                                    let _0_379 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        b in
                                                    let _0_378 =
                                                      let _0_377 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_f in
                                                      let _0_376 =
                                                        let _0_375 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g in
                                                        [_0_375] in
                                                      _0_377 :: _0_376 in
                                                    _0_379 :: _0_378 in
                                                  _0_381 :: _0_380 in
                                                r :: _0_382 in
                                              FStar_List.map
                                                FStar_Syntax_Syntax.as_arg
                                                _0_383 in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              _0_385 _0_384) None
                                             FStar_Range.dummyRange in
                                         mk_repr b wp in
                                       let expected_k =
                                         let _0_403 =
                                           let _0_401 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let _0_400 =
                                             let _0_399 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let _0_398 =
                                               let _0_397 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f in
                                               let _0_396 =
                                                 let _0_395 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     (let _0_386 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_f in
                                                      mk_repr a _0_386) in
                                                 let _0_394 =
                                                   let _0_393 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g in
                                                   let _0_392 =
                                                     let _0_391 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         (let _0_390 =
                                                            let _0_387 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x_a in
                                                            [_0_387] in
                                                          let _0_389 =
                                                            let _0_388 =
                                                              mk_repr b
                                                                wp_g_x in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.mk_Total
                                                              _0_388 in
                                                          FStar_Syntax_Util.arrow
                                                            _0_390 _0_389) in
                                                     [_0_391] in
                                                   _0_393 :: _0_392 in
                                                 _0_395 :: _0_394 in
                                               _0_397 :: _0_396 in
                                             _0_399 :: _0_398 in
                                           _0_401 :: _0_400 in
                                         let _0_402 =
                                           FStar_Syntax_Syntax.mk_Total res in
                                         FStar_Syntax_Util.arrow _0_403
                                           _0_402 in
                                       let uu____619 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env expected_k in
                                       (match uu____619 with
                                        | (expected_k,uu____624,uu____625) ->
                                            let env =
                                              FStar_TypeChecker_Env.set_range
                                                env
                                                (Prims.snd
                                                   ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos in
                                            let env =
                                              let uu___88_629 = env in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___88_629.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___88_629.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___88_629.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___88_629.FStar_TypeChecker_Env.qname_and_index)
                                              } in
                                            let br =
                                              check_and_gen' env
                                                ed.FStar_Syntax_Syntax.bind_repr
                                                expected_k in
                                            br) in
                                 let return_repr =
                                   let x_a =
                                     let _0_404 =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       _0_404 in
                                   let res =
                                     let wp =
                                       (let _0_411 =
                                          let _0_405 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              return_wp in
                                          FStar_All.pipe_right _0_405
                                            Prims.snd in
                                        let _0_410 =
                                          let _0_409 =
                                            let _0_408 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            let _0_407 =
                                              let _0_406 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x_a in
                                              [_0_406] in
                                            _0_408 :: _0_407 in
                                          FStar_List.map
                                            FStar_Syntax_Syntax.as_arg _0_409 in
                                        FStar_Syntax_Syntax.mk_Tm_app _0_411
                                          _0_410) None FStar_Range.dummyRange in
                                     mk_repr a wp in
                                   let expected_k =
                                     let _0_416 =
                                       let _0_414 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let _0_413 =
                                         let _0_412 =
                                           FStar_Syntax_Syntax.mk_binder x_a in
                                         [_0_412] in
                                       _0_414 :: _0_413 in
                                     let _0_415 =
                                       FStar_Syntax_Syntax.mk_Total res in
                                     FStar_Syntax_Util.arrow _0_416 _0_415 in
                                   let uu____651 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env expected_k in
                                   match uu____651 with
                                   | (expected_k,uu____659,uu____660) ->
                                       let env =
                                         FStar_TypeChecker_Env.set_range env
                                           (Prims.snd
                                              ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos in
                                       let uu____663 =
                                         check_and_gen' env
                                           ed.FStar_Syntax_Syntax.return_repr
                                           expected_k in
                                       (match uu____663 with
                                        | (univs,repr) ->
                                            (match univs with
                                             | [] -> ([], repr)
                                             | uu____675 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr.FStar_Syntax_Syntax.pos))))) in
                                 let actions =
                                   let check_action act =
                                     let uu____686 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env
                                         act.FStar_Syntax_Syntax.action_typ in
                                     match uu____686 with
                                     | (act_typ,uu____691,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env act_typ in
                                         ((let uu____695 =
                                             FStar_TypeChecker_Env.debug env
                                               (FStar_Options.Other "ED") in
                                           if uu____695
                                           then
                                             let _0_418 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn in
                                             let _0_417 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               _0_418 _0_417
                                           else ());
                                          (let uu____697 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn in
                                           match uu____697 with
                                           | (act_defn,uu____702,g_a) ->
                                               let act_defn =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant]
                                                   env act_defn in
                                               let act_typ =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant;
                                                   FStar_TypeChecker_Normalize.Eager_unfolding;
                                                   FStar_TypeChecker_Normalize.Beta]
                                                   env act_typ in
                                               let uu____706 =
                                                 let act_typ =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ in
                                                 match act_typ.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____724 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c in
                                                     (match uu____724 with
                                                      | (bs,uu____730) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun in
                                                          let k =
                                                            let _0_419 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res in
                                                            FStar_Syntax_Util.arrow
                                                              bs _0_419 in
                                                          let uu____737 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env k in
                                                          (match uu____737
                                                           with
                                                           | (k,uu____744,g)
                                                               -> (k, g)))
                                                 | uu____746 ->
                                                     Prims.raise
                                                       (FStar_Errors.Error
                                                          (let _0_422 =
                                                             let _0_421 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 act_typ in
                                                             let _0_420 =
                                                               FStar_Syntax_Print.tag_of_term
                                                                 act_typ in
                                                             FStar_Util.format2
                                                               "Actions must have function types (not: %s, a.k.a. %s)"
                                                               _0_421 _0_420 in
                                                           (_0_422,
                                                             (act_defn.FStar_Syntax_Syntax.pos)))) in
                                               (match uu____706 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env act_typ
                                                        expected_k in
                                                    ((let _0_425 =
                                                        let _0_424 =
                                                          let _0_423 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k _0_423 in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a _0_424 in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env _0_425);
                                                     (let act_typ =
                                                        let uu____756 =
                                                          (FStar_Syntax_Subst.compress
                                                             expected_k).FStar_Syntax_Syntax.n in
                                                        match uu____756 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____771 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c in
                                                            (match uu____771
                                                             with
                                                             | (bs,c) ->
                                                                 let uu____778
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c) in
                                                                 (match uu____778
                                                                  with
                                                                  | (a,wp) ->
                                                                    let c =
                                                                    let _0_429
                                                                    =
                                                                    let _0_426
                                                                    =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env a in
                                                                    [_0_426] in
                                                                    let _0_428
                                                                    =
                                                                    let _0_427
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [_0_427] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = _0_429;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = _0_428;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let _0_430
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs _0_430))
                                                        | uu____798 ->
                                                            failwith "" in
                                                      let uu____801 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env act_defn in
                                                      match uu____801 with
                                                      | (univs,act_defn) ->
                                                          let act_typ =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env act_typ in
                                                          let uu___89_807 =
                                                            act in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___89_807.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___89_807.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs;
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ
                                                          }))))) in
                                   FStar_All.pipe_right
                                     ed.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action) in
                                 (repr, bind_repr, return_repr, actions) in
                           match uu____465 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 let _0_431 =
                                   FStar_Syntax_Syntax.mk_Total
                                     ed.FStar_Syntax_Syntax.signature in
                                 FStar_Syntax_Util.arrow
                                   ed.FStar_Syntax_Syntax.binders _0_431 in
                               let uu____823 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t in
                               (match uu____823 with
                                | (univs,t) ->
                                    let signature =
                                      let uu____829 =
                                        let _0_432 =
                                          (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
                                        (effect_params, _0_432) in
                                      match uu____829 with
                                      | ([],uu____832) -> t
                                      | (uu____838,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____839,c)) ->
                                          FStar_Syntax_Util.comp_result c
                                      | uu____851 -> failwith "Impossible" in
                                    let close n ts =
                                      let ts =
                                        let _0_433 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs _0_433 in
                                      let m =
                                        FStar_List.length (Prims.fst ts) in
                                      (let uu____866 =
                                         ((n >= (Prims.parse_int "0")) &&
                                            (Prims.op_Negation
                                               (FStar_Syntax_Util.is_unknown
                                                  (Prims.snd ts))))
                                           && (m <> n) in
                                       if uu____866
                                       then
                                         let error =
                                           if m < n
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic" in
                                         failwith
                                           (let _0_435 =
                                              FStar_Util.string_of_int n in
                                            let _0_434 =
                                              FStar_Syntax_Print.tscheme_to_string
                                                ts in
                                            FStar_Util.format3
                                              "The effect combinator is %s (n=%s) (%s)"
                                              error _0_435 _0_434)
                                       else ());
                                      ts in
                                    let close_action act =
                                      let uu____880 =
                                        close (- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn)) in
                                      match uu____880 with
                                      | (univs,defn) ->
                                          let uu____885 =
                                            close (- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ)) in
                                          (match uu____885 with
                                           | (univs',typ) ->
                                               let uu___90_891 = act in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___90_891.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___90_891.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs;
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               }) in
                                    let nunivs = FStar_List.length univs in
                                    let ed =
                                      let uu___91_896 = ed in
                                      let _0_449 =
                                        close (Prims.parse_int "0") return_wp in
                                      let _0_448 =
                                        close (Prims.parse_int "1") bind_wp in
                                      let _0_447 =
                                        close (Prims.parse_int "0")
                                          if_then_else in
                                      let _0_446 =
                                        close (Prims.parse_int "0") ite_wp in
                                      let _0_445 =
                                        close (Prims.parse_int "0") stronger in
                                      let _0_444 =
                                        close (Prims.parse_int "1") close_wp in
                                      let _0_443 =
                                        close (Prims.parse_int "0") assert_p in
                                      let _0_442 =
                                        close (Prims.parse_int "0") assume_p in
                                      let _0_441 =
                                        close (Prims.parse_int "0") null_wp in
                                      let _0_440 =
                                        close (Prims.parse_int "0")
                                          trivial_wp in
                                      let _0_439 =
                                        Prims.snd
                                          (close (Prims.parse_int "0")
                                             ([], repr)) in
                                      let _0_438 =
                                        close (Prims.parse_int "0")
                                          return_repr in
                                      let _0_437 =
                                        close (Prims.parse_int "1") bind_repr in
                                      let _0_436 =
                                        FStar_List.map close_action actions in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___91_896.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___91_896.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___91_896.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature;
                                        FStar_Syntax_Syntax.ret_wp = _0_449;
                                        FStar_Syntax_Syntax.bind_wp = _0_448;
                                        FStar_Syntax_Syntax.if_then_else =
                                          _0_447;
                                        FStar_Syntax_Syntax.ite_wp = _0_446;
                                        FStar_Syntax_Syntax.stronger = _0_445;
                                        FStar_Syntax_Syntax.close_wp = _0_444;
                                        FStar_Syntax_Syntax.assert_p = _0_443;
                                        FStar_Syntax_Syntax.assume_p = _0_442;
                                        FStar_Syntax_Syntax.null_wp = _0_441;
                                        FStar_Syntax_Syntax.trivial = _0_440;
                                        FStar_Syntax_Syntax.repr = _0_439;
                                        FStar_Syntax_Syntax.return_repr =
                                          _0_438;
                                        FStar_Syntax_Syntax.bind_repr =
                                          _0_437;
                                        FStar_Syntax_Syntax.actions = _0_436
                                      } in
                                    ((let uu____900 =
                                        (FStar_TypeChecker_Env.debug env
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other "ED")) in
                                      if uu____900
                                      then
                                        FStar_Util.print_string
                                          (FStar_Syntax_Print.eff_decl_to_string
                                             false ed)
                                      else ());
                                     ed)))))))
and cps_and_elaborate:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.eff_decl*
        FStar_Syntax_Syntax.sigelt Prims.option)
  =
  fun env  ->
    fun ed  ->
      let uu____904 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature in
      match uu____904 with
      | (effect_binders_un,signature_un) ->
          let uu____914 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un in
          (match uu____914 with
           | (effect_binders,env,uu____925) ->
               let uu____926 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un in
               (match uu____926 with
                | (signature,uu____935) ->
                    let effect_binders =
                      FStar_List.map
                        (fun uu____944  ->
                           match uu____944 with
                           | (bv,qual) ->
                               let _0_451 =
                                 let uu___92_951 = bv in
                                 let _0_450 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___92_951.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___92_951.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = _0_450
                                 } in
                               (_0_451, qual)) effect_binders in
                    let uu____952 =
                      let uu____957 =
                        (FStar_Syntax_Subst.compress signature_un).FStar_Syntax_Syntax.n in
                      match uu____957 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____963)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____978 ->
                          failwith "bad shape for effect-for-free signature" in
                    (match uu____952 with
                     | (a,effect_marker) ->
                         let a =
                           let uu____995 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____995
                           then
                             let _0_452 =
                               Some (FStar_Syntax_Syntax.range_of_bv a) in
                             FStar_Syntax_Syntax.gen_bv "a" _0_452
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check t =
                           let subst =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders in
                           let t = FStar_Syntax_Subst.subst subst t in
                           let uu____1005 =
                             FStar_TypeChecker_TcTerm.tc_term env t in
                           match uu____1005 with
                           | (t,comp,uu____1013) -> (t, comp) in
                         let mk x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____1024 =
                           open_and_check ed.FStar_Syntax_Syntax.repr in
                         (match uu____1024 with
                          | (repr,_comp) ->
                              ((let uu____1035 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "ED") in
                                if uu____1035
                                then
                                  let _0_453 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    _0_453
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange) in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr in
                                let wp_type = recheck_debug "*" env wp_type in
                                let wp_a =
                                  let _0_458 =
                                    mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (let _0_457 =
                                            let _0_456 =
                                              let _0_455 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              let _0_454 =
                                                FStar_Syntax_Syntax.as_implicit
                                                  false in
                                              (_0_455, _0_454) in
                                            [_0_456] in
                                          (wp_type, _0_457))) in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env
                                    _0_458 in
                                let effect_signature =
                                  let binders =
                                    let _0_463 =
                                      let _0_459 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a, _0_459) in
                                    let _0_462 =
                                      let _0_461 =
                                        let _0_460 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a in
                                        FStar_All.pipe_right _0_460
                                          FStar_Syntax_Syntax.mk_binder in
                                      [_0_461] in
                                    _0_463 :: _0_462 in
                                  let binders =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders, effect_marker)) in
                                let effect_signature =
                                  recheck_debug
                                    "turned into the effect signature" env
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       (Prims.strcat
                                          (FStar_Ident.text_of_lid
                                             ed.FStar_Syntax_Syntax.mname)
                                          (Prims.strcat "_" name)))
                                    FStar_Range.dummyRange in
                                let elaborate_and_star dmff_env item =
                                  let uu____1087 = item in
                                  match uu____1087 with
                                  | (u_item,item) ->
                                      let uu____1099 = open_and_check item in
                                      (match uu____1099 with
                                       | (item,item_comp) ->
                                           ((let uu____1109 =
                                               Prims.op_Negation
                                                 (FStar_Syntax_Util.is_total_lcomp
                                                    item_comp) in
                                             if uu____1109
                                             then
                                               Prims.raise
                                                 (FStar_Errors.Err
                                                    (let _0_465 =
                                                       FStar_Syntax_Print.term_to_string
                                                         item in
                                                     let _0_464 =
                                                       FStar_Syntax_Print.lcomp_to_string
                                                         item_comp in
                                                     FStar_Util.format2
                                                       "Computation for [%s] is not total : %s !"
                                                       _0_465 _0_464))
                                             else ());
                                            (let uu____1111 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env item in
                                             match uu____1111 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp =
                                                   recheck_debug "*" env
                                                     item_wp in
                                                 let item_elab =
                                                   recheck_debug "_" env
                                                     item_elab in
                                                 (dmff_env, item_t, item_wp,
                                                   item_elab)))) in
                                let uu____1124 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr in
                                match uu____1124 with
                                | (dmff_env,uu____1135,bind_wp,bind_elab) ->
                                    let uu____1138 =
                                      elaborate_and_star dmff_env
                                        ed.FStar_Syntax_Syntax.return_repr in
                                    (match uu____1138 with
                                     | (dmff_env,uu____1149,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1153 =
                                             (FStar_Syntax_Subst.compress
                                                return_wp).FStar_Syntax_Syntax.n in
                                           match uu____1153 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1189 =
                                                 let uu____1197 =
                                                   let _0_466 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] _0_466 in
                                                 match uu____1197 with
                                                 | (b1::b2::[],body) ->
                                                     (b1, b2, body)
                                                 | uu____1238 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____1189 with
                                                | (b1,b2,body) ->
                                                    let env0 =
                                                      let _0_467 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env in
                                                      FStar_TypeChecker_Env.push_binders
                                                        _0_467 [b1; b2] in
                                                    let wp_b1 =
                                                      let _0_472 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_app
                                                             (let _0_471 =
                                                                let _0_470 =
                                                                  let _0_469
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (Prims.fst
                                                                    b1) in
                                                                  let _0_468
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                  (_0_469,
                                                                    _0_468) in
                                                                [_0_470] in
                                                              (wp_type,
                                                                _0_471))) in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 _0_472 in
                                                    let uu____1274 =
                                                      let _0_474 =
                                                        let _0_473 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          body _0_473 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        _0_474 in
                                                    (match uu____1274 with
                                                     | (bs,body,what') ->
                                                         let t2 =
                                                           (Prims.fst b2).FStar_Syntax_Syntax.sort in
                                                         let pure_wp_type =
                                                           FStar_TypeChecker_DMFF.double_star
                                                             t2 in
                                                         let wp =
                                                           FStar_Syntax_Syntax.gen_bv
                                                             "wp" None
                                                             pure_wp_type in
                                                         let body =
                                                           (let _0_478 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp in
                                                            let _0_477 =
                                                              let _0_476 =
                                                                let _0_475 =
                                                                  FStar_Syntax_Util.abs
                                                                    [b2] body
                                                                    what' in
                                                                (_0_475,
                                                                  None) in
                                                              [_0_476] in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              _0_478 _0_477)
                                                             None
                                                             FStar_Range.dummyRange in
                                                         let _0_482 =
                                                           let _0_480 =
                                                             let _0_479 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp in
                                                             [_0_479] in
                                                           b1 :: _0_480 in
                                                         let _0_481 =
                                                           FStar_Syntax_Util.abs
                                                             bs body what in
                                                         FStar_Syntax_Util.abs
                                                           _0_482 _0_481
                                                           (Some
                                                              (FStar_Util.Inr
                                                                 (FStar_Syntax_Const.effect_GTot_lid,
                                                                   [])))))
                                           | uu____1342 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let return_wp =
                                           let uu____1344 =
                                             (FStar_Syntax_Subst.compress
                                                return_wp).FStar_Syntax_Syntax.n in
                                           match uu____1344 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let _0_483 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] _0_483
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1395 ->
                                               failwith
                                                 "unexpected shape for return" in
                                         let bind_wp =
                                           let uu____1397 =
                                             (FStar_Syntax_Subst.compress
                                                bind_wp).FStar_Syntax_Syntax.n in
                                           match uu____1397 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None in
                                               let _0_486 =
                                                 let _0_485 =
                                                   let _0_484 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       (mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             r)) in
                                                   [_0_484] in
                                                 FStar_List.append _0_485
                                                   binders in
                                               FStar_Syntax_Util.abs _0_486
                                                 body what
                                           | uu____1424 ->
                                               failwith
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let _0_488 =
                                                mk
                                                  (FStar_Syntax_Syntax.Tm_app
                                                     (let _0_487 =
                                                        Prims.snd
                                                          (FStar_Syntax_Util.args_of_binders
                                                             effect_binders) in
                                                      (t, _0_487))) in
                                              FStar_Syntax_Subst.close
                                                effect_binders _0_488) in
                                         let register name item =
                                           let uu____1451 =
                                             let _0_490 = mk_lid name in
                                             let _0_489 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders item None in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env _0_490 _0_489 in
                                           match uu____1451 with
                                           | (sigelt,fv) ->
                                               ((let _0_492 =
                                                   let _0_491 =
                                                     FStar_ST.read sigelts in
                                                   sigelt :: _0_491 in
                                                 FStar_ST.write sigelts
                                                   _0_492);
                                                fv) in
                                         let lift_from_pure_wp =
                                           register "lift_from_pure"
                                             lift_from_pure_wp in
                                         let return_wp =
                                           register "return_wp" return_wp in
                                         ((let _0_494 =
                                             let _0_493 =
                                               FStar_ST.read sigelts in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: _0_493 in
                                           FStar_ST.write sigelts _0_494);
                                          (let return_elab =
                                             register "return_elab"
                                               return_elab in
                                           (let _0_496 =
                                              let _0_495 =
                                                FStar_ST.read sigelts in
                                              (FStar_Syntax_Syntax.Sig_pragma
                                                 ((FStar_Syntax_Syntax.SetOptions
                                                     "--admit_smt_queries false"),
                                                   FStar_Range.dummyRange))
                                                :: _0_495 in
                                            FStar_ST.write sigelts _0_496);
                                           (let bind_wp =
                                              register "bind_wp" bind_wp in
                                            (let _0_498 =
                                               let _0_497 =
                                                 FStar_ST.read sigelts in
                                               (FStar_Syntax_Syntax.Sig_pragma
                                                  ((FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"),
                                                    FStar_Range.dummyRange))
                                                 :: _0_497 in
                                             FStar_ST.write sigelts _0_498);
                                            (let bind_elab =
                                               register "bind_elab" bind_elab in
                                             (let _0_500 =
                                                let _0_499 =
                                                  FStar_ST.read sigelts in
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   ((FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries false"),
                                                     FStar_Range.dummyRange))
                                                  :: _0_499 in
                                              FStar_ST.write sigelts _0_500);
                                             (let uu____1501 =
                                                FStar_List.fold_left
                                                  (fun uu____1508  ->
                                                     fun action  ->
                                                       match uu____1508 with
                                                       | (dmff_env,actions)
                                                           ->
                                                           let uu____1520 =
                                                             elaborate_and_star
                                                               dmff_env
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn)) in
                                                           (match uu____1520
                                                            with
                                                            | (dmff_env,action_t,action_wp,action_elab)
                                                                ->
                                                                let name =
                                                                  ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
                                                                let action_typ_with_wp
                                                                  =
                                                                  FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env
                                                                    action_t
                                                                    action_wp in
                                                                let action_elab
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab in
                                                                let action_typ_with_wp
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp in
                                                                let _0_504 =
                                                                  let _0_503
                                                                    =
                                                                    let uu___93_1537
                                                                    = action in
                                                                    let _0_502
                                                                    =
                                                                    apply_close
                                                                    action_elab in
                                                                    let _0_501
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___93_1537.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___93_1537.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___93_1537.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    = _0_502;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    = _0_501
                                                                    } in
                                                                  _0_503 ::
                                                                    actions in
                                                                (dmff_env,
                                                                  _0_504)))
                                                  (dmff_env, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____1501 with
                                              | (dmff_env,actions) ->
                                                  let actions =
                                                    FStar_List.rev actions in
                                                  let repr =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a in
                                                    let binders =
                                                      let _0_507 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a in
                                                      let _0_506 =
                                                        let _0_505 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [_0_505] in
                                                      _0_507 :: _0_506 in
                                                    let _0_514 =
                                                      let _0_513 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_app
                                                             (let _0_511 =
                                                                let _0_510 =
                                                                  let _0_509
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                  let _0_508
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                  (_0_509,
                                                                    _0_508) in
                                                                [_0_510] in
                                                              (repr, _0_511))) in
                                                      let _0_512 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env _0_513
                                                        _0_512 in
                                                    FStar_Syntax_Util.abs
                                                      binders _0_514 None in
                                                  let repr =
                                                    recheck_debug "FC" env
                                                      repr in
                                                  let repr =
                                                    register "repr" repr in
                                                  let uu____1568 =
                                                    let uu____1573 =
                                                      (let _0_515 =
                                                         FStar_Syntax_Subst.compress
                                                           wp_type in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.unascribe
                                                         _0_515).FStar_Syntax_Syntax.n in
                                                    match uu____1573 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow,uu____1581)
                                                        ->
                                                        let uu____1608 =
                                                          let uu____1617 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow in
                                                          match uu____1617
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____1648 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____1608
                                                         with
                                                         | (type_param,effect_param,arrow)
                                                             ->
                                                             let uu____1676 =
                                                               (let _0_516 =
                                                                  FStar_Syntax_Subst.compress
                                                                    arrow in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Util.unascribe
                                                                  _0_516).FStar_Syntax_Syntax.n in
                                                             (match uu____1676
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____1693
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____1693
                                                                   with
                                                                   | 
                                                                   (wp_binders,c)
                                                                    ->
                                                                    let uu____1702
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____1713
                                                                     ->
                                                                    match uu____1713
                                                                    with
                                                                    | 
                                                                    (bv,uu____1717)
                                                                    ->
                                                                    let _0_518
                                                                    =
                                                                    let _0_517
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    _0_517
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param)) in
                                                                    FStar_All.pipe_right
                                                                    _0_518
                                                                    Prims.op_Negation)
                                                                    wp_binders in
                                                                    (match uu____1702
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
                                                                    uu____1749
                                                                    ->
                                                                    failwith
                                                                    (let _0_519
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    _0_519) in
                                                                    let _0_521
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c in
                                                                    let _0_520
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None in
                                                                    (_0_521,
                                                                    _0_520)))
                                                              | uu____1764 ->
                                                                  failwith
                                                                    (
                                                                    let _0_522
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    _0_522)))
                                                    | uu____1769 ->
                                                        failwith
                                                          (let _0_523 =
                                                             FStar_Syntax_Print.term_to_string
                                                               wp_type in
                                                           FStar_Util.format1
                                                             "Impossible: pre/post abs %s"
                                                             _0_523) in
                                                  (match uu____1568 with
                                                   | (pre,post) ->
                                                       (Prims.ignore
                                                          (register "pre" pre);
                                                        Prims.ignore
                                                          (register "post"
                                                             post);
                                                        Prims.ignore
                                                          (register "wp"
                                                             wp_type);
                                                        (let ed =
                                                           let uu___94_1789 =
                                                             ed in
                                                           let _0_534 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders in
                                                           let _0_533 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders
                                                               effect_signature in
                                                           let _0_532 =
                                                             let _0_524 =
                                                               apply_close
                                                                 return_wp in
                                                             ([], _0_524) in
                                                           let _0_531 =
                                                             let _0_525 =
                                                               apply_close
                                                                 bind_wp in
                                                             ([], _0_525) in
                                                           let _0_530 =
                                                             apply_close repr in
                                                           let _0_529 =
                                                             let _0_526 =
                                                               apply_close
                                                                 return_elab in
                                                             ([], _0_526) in
                                                           let _0_528 =
                                                             let _0_527 =
                                                               apply_close
                                                                 bind_elab in
                                                             ([], _0_527) in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = _0_534;
                                                             FStar_Syntax_Syntax.signature
                                                               = _0_533;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = _0_532;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = _0_531;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___94_1789.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = _0_530;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = _0_529;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = _0_528;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions
                                                           } in
                                                         let uu____1802 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env
                                                             effect_binders a
                                                             wp_a ed in
                                                         match uu____1802
                                                         with
                                                         | (sigelts',ed) ->
                                                             ((let uu____1813
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____1813
                                                               then
                                                                 FStar_Util.print_string
                                                                   (FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed)
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders)
                                                                    =
                                                                    (Prims.parse_int
                                                                    "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let _0_536
                                                                    =
                                                                    Some
                                                                    (let _0_535
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp in
                                                                    ([],
                                                                    _0_535)) in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Syntax_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    = _0_536;
                                                                    FStar_Syntax_Syntax.lift
                                                                    = None
                                                                    } in
                                                                   Some
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    (lift_from_pure,
                                                                    FStar_Range.dummyRange))
                                                                 else None in
                                                               let _0_538 =
                                                                 let _0_537 =
                                                                   FStar_List.rev
                                                                    (FStar_ST.read
                                                                    sigelts) in
                                                                 FStar_List.append
                                                                   _0_537
                                                                   sigelts' in
                                                               (_0_538, ed,
                                                                 lift_from_pure_opt))))))))))))))))))
and tc_lex_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          match ses with
          | (FStar_Syntax_Syntax.Sig_inductive_typ
              (lex_t,[],[],t,uu____1853,uu____1854,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top,[],_t_top,_lex_t_top,_0_539,[],uu____1859,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_540,[],uu____1864,r2))::[]
              when
              ((_0_539 = (Prims.parse_int "0")) &&
                 (_0_540 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top
                       FStar_Syntax_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Syntax_Const.lexcons_lid))
              ->
              let u = FStar_Syntax_Syntax.new_univ_name (Some r) in
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r in
              let t = FStar_Syntax_Subst.close_univ_vars [u] t in
              let tc =
                FStar_Syntax_Syntax.Sig_inductive_typ
                  (lex_t, [u], [], t, [],
                    [FStar_Syntax_Const.lextop_lid;
                    FStar_Syntax_Const.lexcons_lid], [], r) in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1) in
              let lex_top_t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_uinst
                      (let _0_541 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Syntax_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant None in
                       (_0_541, [FStar_Syntax_Syntax.U_name utop])))) None r1 in
              let lex_top_t =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
              let dc_lextop =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_top, [utop], lex_top_t, FStar_Syntax_Const.lex_t_lid,
                    (Prims.parse_int "0"), [], [], r1) in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2) in
              let lex_cons_t =
                let a =
                  let _0_542 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) _0_542 in
                let hd =
                  let _0_543 = FStar_Syntax_Syntax.bv_to_name a in
                  FStar_Syntax_Syntax.new_bv (Some r2) _0_543 in
                let tl =
                  let _0_545 =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_uinst
                          (let _0_544 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant None in
                           (_0_544, [FStar_Syntax_Syntax.U_name ucons2]))))
                      None r2 in
                  FStar_Syntax_Syntax.new_bv (Some r2) _0_545 in
                let res =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uinst
                        (let _0_546 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Syntax_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant None in
                         (_0_546,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])))) None r2 in
                let _0_547 = FStar_Syntax_Syntax.mk_Total res in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd, None);
                  (tl, None)] _0_547 in
              let lex_cons_t =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t in
              let dc_lexcons =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons, [ucons1; ucons2], lex_cons_t,
                    FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), [],
                    [], r2) in
              FStar_Syntax_Syntax.Sig_bundle
                (let _0_548 = FStar_TypeChecker_Env.get_range env in
                 ([tc; dc_lextop; dc_lexcons], [], lids, _0_548))
          | uu____1986 ->
              failwith
                (let _0_549 =
                   FStar_Syntax_Print.sigelt_to_string
                     (FStar_Syntax_Syntax.Sig_bundle
                        (ses, [], lids, FStar_Range.dummyRange)) in
                 FStar_Util.format1 "Unexpected lex_t: %s\n" _0_549)
and tc_assume:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.formula ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun lid  ->
      fun phi  ->
        fun quals  ->
          fun r  ->
            let env = FStar_TypeChecker_Env.set_range env r in
            let uu____1998 = FStar_Syntax_Util.type_u () in
            match uu____1998 with
            | (k,uu____2002) ->
                let phi =
                  let _0_550 = tc_check_trivial_guard env phi k in
                  FStar_All.pipe_right _0_550
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env) in
                (FStar_TypeChecker_Util.check_uvars r phi;
                 FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r))
and tc_inductive:
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env0 = env in
          let uu____2014 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids in
          match uu____2014 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let _0_551 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas in
                FStar_All.pipe_right _0_551 FStar_List.flatten in
              ((let uu____2038 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ()) in
                if uu____2038
                then ()
                else
                  (let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env in
                        if Prims.op_Negation b
                        then
                          let uu____2044 =
                            match ty with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2050,uu____2051,uu____2052,uu____2053,uu____2054,uu____2055,r)
                                -> (lid, r)
                            | uu____2063 -> failwith "Impossible!" in
                          match uu____2044 with
                          | (lid,r) ->
                              FStar_Errors.report r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2072 =
                  let lid =
                    let ty = FStar_List.hd tcs in
                    match ty with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2076,uu____2077,uu____2078,uu____2079,uu____2080,uu____2081,uu____2082)
                        -> lid
                    | uu____2089 -> failwith "Impossible" in
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"] in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals in
                let uu____2095 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq in
                if uu____2095
                then ([sig_bndle], data_ops_ses)
                else
                  (let is_unopteq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals in
                   let ses =
                     if is_unopteq
                     then
                       FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                     else
                       FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume in
                   let _0_554 =
                     let _0_553 =
                       FStar_Syntax_Syntax.Sig_bundle
                         (let _0_552 = FStar_TypeChecker_Env.get_range env0 in
                          ((FStar_List.append tcs datas), quals, lids,
                            _0_552)) in
                     _0_553 :: ses in
                   (_0_554, data_ops_ses))))
and tc_decl:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_TypeChecker_Env.env*
        FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun se  ->
      let env = set_hint_correlator env se in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (match se with
       | FStar_Syntax_Syntax.Sig_inductive_typ _
         |FStar_Syntax_Syntax.Sig_datacon _ ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))
           ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let se = tc_lex_t env ses quals lids in
           let _0_555 = FStar_TypeChecker_Env.push_sigelt env se in
           ([se], _0_555, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____2163 = tc_inductive env ses quals lids in
           (match uu____2163 with
            | (ses,projectors_ses) ->
                let env =
                  FStar_List.fold_left
                    (fun env'  ->
                       fun se  -> FStar_TypeChecker_Env.push_sigelt env' se)
                    env ses in
                (ses, env, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma (p,r) ->
           let set_options t s =
             let uu____2193 = FStar_Options.set_options t s in
             match uu____2193 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s), r)) in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], env, []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options FStar_Options.Set o; ([se], env, []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let _0_556 = FStar_Options.restore_cmd_line_options false in
                  FStar_All.pipe_right _0_556 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options FStar_Options.Reset s);
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
           let uu____2218 = cps_and_elaborate env ne in
           (match uu____2218 with
            | (ses,ne,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [FStar_Syntax_Syntax.Sig_new_effect (ne, r); lift]
                  | None  -> [FStar_Syntax_Syntax.Sig_new_effect (ne, r)] in
                ([], env, (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect (ne,r) ->
           let ne = tc_eff_decl env ne in
           let se = FStar_Syntax_Syntax.Sig_new_effect (ne, r) in
           let env = FStar_TypeChecker_Env.push_sigelt env se in
           let uu____2247 =
             FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____2258  ->
                     fun a  ->
                       match uu____2258 with
                       | (env,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne.FStar_Syntax_Syntax.mname a in
                           let _0_557 =
                             FStar_TypeChecker_Env.push_sigelt env se_let in
                           (_0_557, (se_let :: ses))) (env, [se])) in
           (match uu____2247 with | (env,ses) -> ([se], env, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub,r) ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub.FStar_Syntax_Syntax.source in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub.FStar_Syntax_Syntax.target in
           let uu____2288 =
             let _0_558 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source _0_558 in
           (match uu____2288 with
            | (a,wp_a_src) ->
                let uu____2304 =
                  let _0_559 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub.FStar_Syntax_Syntax.target in
                  monad_signature env sub.FStar_Syntax_Syntax.target _0_559 in
                (match uu____2304 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let _0_562 =
                         let _0_561 =
                           FStar_Syntax_Syntax.NT
                             (let _0_560 = FStar_Syntax_Syntax.bv_to_name a in
                              (b, _0_560)) in
                         [_0_561] in
                       FStar_Syntax_Subst.subst _0_562 wp_b_tgt in
                     let expected_k =
                       let _0_567 =
                         let _0_565 = FStar_Syntax_Syntax.mk_binder a in
                         let _0_564 =
                           let _0_563 =
                             FStar_Syntax_Syntax.null_binder wp_a_src in
                           [_0_563] in
                         _0_565 :: _0_564 in
                       let _0_566 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                       FStar_Syntax_Util.arrow _0_567 _0_566 in
                     let repr_type eff_name a wp =
                       let no_reify l =
                         Prims.raise
                           (FStar_Errors.Error
                              (let _0_569 =
                                 FStar_Util.format1
                                   "Effect %s cannot be reified"
                                   l.FStar_Ident.str in
                               let _0_568 =
                                 FStar_TypeChecker_Env.get_range env in
                               (_0_569, _0_568))) in
                       let uu____2344 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____2344 with
                       | None  -> no_reify eff_name
                       | Some ed ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ([], (ed.FStar_Syntax_Syntax.repr)) in
                           let uu____2351 =
                             Prims.op_Negation
                               (FStar_All.pipe_right
                                  ed.FStar_Syntax_Syntax.qualifiers
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Reifiable)) in
                           if uu____2351
                           then no_reify eff_name
                           else
                             (let _0_574 =
                                FStar_TypeChecker_Env.get_range env in
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (let _0_573 =
                                       let _0_572 =
                                         FStar_Syntax_Syntax.as_arg a in
                                       let _0_571 =
                                         let _0_570 =
                                           FStar_Syntax_Syntax.as_arg wp in
                                         [_0_570] in
                                       _0_572 :: _0_571 in
                                     (repr, _0_573)))) None _0_574) in
                     let uu____2365 =
                       match ((sub.FStar_Syntax_Syntax.lift),
                               (sub.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some (uu____2380,lift_wp)) ->
                           let _0_575 = check_and_gen env lift_wp expected_k in
                           (lift, _0_575)
                       | (Some (what,lift),None ) ->
                           let dmff_env =
                             FStar_TypeChecker_DMFF.empty env
                               (FStar_TypeChecker_TcTerm.tc_constant
                                  FStar_Range.dummyRange) in
                           let uu____2407 =
                             FStar_TypeChecker_DMFF.star_expr dmff_env lift in
                           (match uu____2407 with
                            | (uu____2414,lift_wp,lift_elab) ->
                                let uu____2417 =
                                  recheck_debug "lift-wp" env lift_wp in
                                let uu____2418 =
                                  recheck_debug "lift-elab" env lift_elab in
                                ((Some ([], lift_elab)), ([], lift_wp))) in
                     (match uu____2365 with
                      | (lift,lift_wp) ->
                          let lax = env.FStar_TypeChecker_Env.lax in
                          let env =
                            let uu___95_2442 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___95_2442.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___95_2442.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___95_2442.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___95_2442.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___95_2442.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___95_2442.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___95_2442.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___95_2442.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___95_2442.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___95_2442.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___95_2442.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___95_2442.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___95_2442.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___95_2442.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___95_2442.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___95_2442.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___95_2442.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___95_2442.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___95_2442.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___95_2442.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___95_2442.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___95_2442.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___95_2442.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let lift =
                            match lift with
                            | None  -> None
                            | Some (uu____2446,lift) ->
                                let uu____2453 =
                                  let _0_576 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env sub.FStar_Syntax_Syntax.source in
                                  monad_signature env
                                    sub.FStar_Syntax_Syntax.source _0_576 in
                                (match uu____2453 with
                                 | (a,wp_a_src) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a in
                                     let repr_f =
                                       repr_type
                                         sub.FStar_Syntax_Syntax.source a_typ
                                         wp_a_typ in
                                     let repr_result =
                                       let lift_wp =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env (Prims.snd lift_wp) in
                                       let lift_wp_a =
                                         let _0_581 =
                                           FStar_TypeChecker_Env.get_range
                                             env in
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (let _0_580 =
                                                  let _0_579 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      a_typ in
                                                  let _0_578 =
                                                    let _0_577 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp_a_typ in
                                                    [_0_577] in
                                                  _0_579 :: _0_578 in
                                                (lift_wp, _0_580)))) None
                                           _0_581 in
                                       repr_type
                                         sub.FStar_Syntax_Syntax.target a_typ
                                         lift_wp_a in
                                     let expected_k =
                                       let _0_588 =
                                         let _0_586 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let _0_585 =
                                           let _0_584 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a in
                                           let _0_583 =
                                             let _0_582 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f in
                                             [_0_582] in
                                           _0_584 :: _0_583 in
                                         _0_586 :: _0_585 in
                                       let _0_587 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result in
                                       FStar_Syntax_Util.arrow _0_588 _0_587 in
                                     let uu____2491 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env expected_k in
                                     (match uu____2491 with
                                      | (expected_k,uu____2497,uu____2498) ->
                                          let lift =
                                            check_and_gen env lift expected_k in
                                          Some lift)) in
                          let env =
                            let uu___96_2501 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___96_2501.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___96_2501.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___96_2501.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___96_2501.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___96_2501.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___96_2501.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___96_2501.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___96_2501.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___96_2501.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___96_2501.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___96_2501.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___96_2501.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___96_2501.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___96_2501.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___96_2501.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___96_2501.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___96_2501.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___96_2501.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = lax;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___96_2501.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___96_2501.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___96_2501.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___96_2501.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___96_2501.FStar_TypeChecker_Env.qname_and_index)
                            } in
                          let sub =
                            let uu___97_2503 = sub in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___97_2503.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___97_2503.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = (Some lift_wp);
                              FStar_Syntax_Syntax.lift = lift
                            } in
                          let se =
                            FStar_Syntax_Syntax.Sig_sub_effect (sub, r) in
                          let env = FStar_TypeChecker_Env.push_sigelt env se in
                          ([se], env, []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env in
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____2522 = FStar_Syntax_Subst.open_comp tps c in
           (match uu____2522 with
            | (tps,c) ->
                let uu____2532 = FStar_TypeChecker_TcTerm.tc_tparams env tps in
                (match uu____2532 with
                 | (tps,env,us) ->
                     let uu____2544 = FStar_TypeChecker_TcTerm.tc_comp env c in
                     (match uu____2544 with
                      | (c,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env g;
                           (let tps = FStar_Syntax_Subst.close_binders tps in
                            let c = FStar_Syntax_Subst.close_comp tps c in
                            let uu____2559 =
                              let _0_589 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                                  None r in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 _0_589 in
                            match uu____2559 with
                            | (uvs,t) ->
                                let uu____2577 =
                                  let uu____2585 =
                                    let _0_590 =
                                      (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
                                    (tps, _0_590) in
                                  match uu____2585 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____2595,c)) -> ([], c)
                                  | (uu____2619,FStar_Syntax_Syntax.Tm_arrow
                                     (tps,c)) -> (tps, c)
                                  | uu____2637 -> failwith "Impossible" in
                                (match uu____2577 with
                                 | (tps,c) ->
                                     (if
                                        ((FStar_List.length uvs) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____2667 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs t in
                                         match uu____2667 with
                                         | (uu____2670,t) ->
                                             Prims.raise
                                               (FStar_Errors.Error
                                                  (let _0_594 =
                                                     let _0_593 =
                                                       FStar_Syntax_Print.lid_to_string
                                                         lid in
                                                     let _0_592 =
                                                       FStar_All.pipe_right
                                                         (FStar_List.length
                                                            uvs)
                                                         FStar_Util.string_of_int in
                                                     let _0_591 =
                                                       FStar_Syntax_Print.term_to_string
                                                         t in
                                                     FStar_Util.format3
                                                       "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                       _0_593 _0_592 _0_591 in
                                                   (_0_594, r))))
                                      else ();
                                      (let se =
                                         FStar_Syntax_Syntax.Sig_effect_abbrev
                                           (lid, uvs, tps, c, tags, flags, r) in
                                       let env =
                                         FStar_TypeChecker_Env.push_sigelt
                                           env0 se in
                                       ([se], env, [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals,_)
         |FStar_Syntax_Syntax.Sig_let (_,_,_,quals,_) when
           FStar_All.pipe_right quals
             (FStar_Util.for_some
                (fun uu___77_2703  ->
                   match uu___77_2703 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____2704 -> false))
           -> ([], env, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let uu____2715 =
             if uvs = []
             then
               let _0_595 = Prims.fst (FStar_Syntax_Util.type_u ()) in
               check_and_gen env t _0_595
             else
               (let uu____2717 = FStar_Syntax_Subst.open_univ_vars uvs t in
                match uu____2717 with
                | (uvs,t) ->
                    let t =
                      let _0_596 = Prims.fst (FStar_Syntax_Util.type_u ()) in
                      tc_check_trivial_guard env t _0_596 in
                    let t =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env t in
                    let _0_597 = FStar_Syntax_Subst.close_univ_vars uvs t in
                    (uvs, _0_597)) in
           (match uu____2715 with
            | (uvs,t) ->
                let se =
                  FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) in
                let env = FStar_TypeChecker_Env.push_sigelt env se in
                ([se], env, []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi,quals,r) ->
           let se = tc_assume env lid phi quals r in
           let env = FStar_TypeChecker_Env.push_sigelt env se in
           ([se], env, [])
       | FStar_Syntax_Syntax.Sig_main (e,r) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let env =
             FStar_TypeChecker_Env.set_expected_typ env
               FStar_TypeChecker_Common.t_unit in
           let uu____2753 = FStar_TypeChecker_TcTerm.tc_term env e in
           (match uu____2753 with
            | (e,c,g1) ->
                let uu____2765 =
                  let _0_600 =
                    Some
                      (FStar_Syntax_Util.ml_comp
                         FStar_TypeChecker_Common.t_unit r) in
                  let _0_599 =
                    let _0_598 = c.FStar_Syntax_Syntax.comp () in (e, _0_598) in
                  FStar_TypeChecker_TcTerm.check_expected_effect env _0_600
                    _0_599 in
                (match uu____2765 with
                 | (e,uu____2777,g) ->
                     ((let _0_601 = FStar_TypeChecker_Rel.conj_guard g1 g in
                       FStar_TypeChecker_Rel.force_trivial_guard env _0_601);
                      (let se = FStar_Syntax_Syntax.Sig_main (e, r) in
                       let env = FStar_TypeChecker_Env.push_sigelt env se in
                       ([se], env, [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,r,lids,quals,attrs) ->
           let env = FStar_TypeChecker_Env.set_range env r in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____2821 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q') in
                 if uu____2821
                 then Some q
                 else
                   Prims.raise
                     (FStar_Errors.Error
                        (let _0_605 =
                           let _0_604 = FStar_Syntax_Print.lid_to_string l in
                           let _0_603 = FStar_Syntax_Print.quals_to_string q in
                           let _0_602 = FStar_Syntax_Print.quals_to_string q' in
                           FStar_Util.format3
                             "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                             _0_604 _0_603 _0_602 in
                         (_0_605, r))) in
           let uu____2832 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____2853  ->
                     fun lb  ->
                       match uu____2853 with
                       | (gen,lbs,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                           let uu____2877 =
                             let uu____2883 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                             match uu____2883 with
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen, lb, quals_opt)
                             | Some ((uvs,tval),quals) ->
                                 let quals_opt =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____2935 ->
                                       FStar_Errors.warn r
                                         "Annotation from val declaration overrides inline type annotation");
                                  if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    Prims.raise
                                      (FStar_Errors.Error
                                         ("Inline universes are incoherent with annotation from val declaration",
                                           r))
                                  else ();
                                  (let _0_606 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef)) in
                                   (false, _0_606, quals_opt))) in
                           (match uu____2877 with
                            | (gen,lb,quals_opt) ->
                                (gen, (lb :: lbs), quals_opt)))
                  (true, [], (if quals = [] then None else Some quals))) in
           (match uu____2832 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____2996 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___78_2998  ->
                                match uu___78_2998 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____2999 -> false)) in
                      if uu____2996
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q in
                let lbs' = FStar_List.rev lbs' in
                let e =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_let
                        (let _0_607 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                FStar_Const.Const_unit) None r in
                         (((Prims.fst lbs), lbs'), _0_607)))) None r in
                let uu____3030 =
                  let uu____3036 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___98_3040 = env in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___98_3040.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___98_3040.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___98_3040.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___98_3040.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___98_3040.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___98_3040.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___98_3040.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___98_3040.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___98_3040.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___98_3040.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___98_3040.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___98_3040.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___98_3040.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___98_3040.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___98_3040.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___98_3040.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___98_3040.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___98_3040.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___98_3040.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___98_3040.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___98_3040.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___98_3040.FStar_TypeChecker_Env.qname_and_index)
                       }) e in
                  match uu____3036 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs,e);
                       FStar_Syntax_Syntax.tk = uu____3048;
                       FStar_Syntax_Syntax.pos = uu____3049;
                       FStar_Syntax_Syntax.vars = uu____3050;_},uu____3051,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals =
                        match e.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3070,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____3075 -> quals in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs, r, lids, quals, attrs)), lbs)
                  | uu____3085 -> failwith "impossible" in
                (match uu____3030 with
                 | (se,lbs) ->
                     ((let uu____3108 = log env in
                       if uu____3108
                       then
                         let _0_612 =
                           let _0_611 =
                             FStar_All.pipe_right (Prims.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____3115 =
                                         let _0_608 =
                                           ((FStar_Util.right
                                               lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env _0_608 in
                                       match uu____3115 with
                                       | None  -> true
                                       | uu____3127 -> false in
                                     if should_log
                                     then
                                       let _0_610 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname in
                                       let _0_609 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp in
                                       FStar_Util.format2 "let %s : %s"
                                         _0_610 _0_609
                                     else "")) in
                           FStar_All.pipe_right _0_611
                             (FStar_String.concat "\n") in
                         FStar_Util.print1 "%s\n" _0_612
                       else ());
                      (let env = FStar_TypeChecker_Env.push_sigelt env se in
                       ([se], env, []))))))
let for_export:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Ident.lident Prims.list)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___79_3160  ->
                match uu___79_3160 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____3161 -> false)) in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____3169 -> false in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____3174 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____3187,r) ->
          let uu____3195 = is_abstract quals in
          if uu____3195
          then
            let for_export_bundle se uu____3214 =
              match uu____3214 with
              | (out,hidden) ->
                  (match se with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____3237,uu____3238,quals,r) ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (let _0_614 =
                              let _0_613 = FStar_Syntax_Syntax.mk_Total t in
                              FStar_Syntax_Util.arrow bs _0_613 in
                            (l, us, _0_614, (FStar_Syntax_Syntax.Assumption
                              :: FStar_Syntax_Syntax.New :: quals), r)) in
                       ((dec :: out), hidden)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____3256,uu____3257,uu____3258,uu____3259,r)
                       ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, us, t, [FStar_Syntax_Syntax.Assumption], r) in
                       ((dec :: out), (l :: hidden))
                   | uu____3269 -> (out, hidden)) in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume
          (uu____3281,uu____3282,quals,uu____3284) ->
          let uu____3287 = is_abstract quals in
          if uu____3287 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____3304 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc) in
          if uu____3304
          then
            ([FStar_Syntax_Syntax.Sig_declare_typ
                (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
              hidden))
          else
            (let uu____3314 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___80_3316  ->
                       match uu___80_3316 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____3319 -> false)) in
             if uu____3314 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____3329 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____3341,uu____3342,quals,uu____3344) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____3362 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
          if uu____3362
          then ([], hidden)
          else
            (let dec =
               FStar_Syntax_Syntax.Sig_declare_typ
                 (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                   (lb.FStar_Syntax_Syntax.lbunivs),
                   (lb.FStar_Syntax_Syntax.lbtyp),
                   [FStar_Syntax_Syntax.Assumption],
                   (FStar_Ident.range_of_lid lid)) in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____3386) ->
          let uu____3393 = is_abstract quals in
          if uu____3393
          then
            let _0_616 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      FStar_Syntax_Syntax.Sig_declare_typ
                        (let _0_615 =
                           ((FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                         (_0_615, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp),
                           (FStar_Syntax_Syntax.Assumption :: quals), r)))) in
            (_0_616, hidden)
          else ([se], hidden)
let tc_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list* FStar_Syntax_Syntax.sigelt
        Prims.list* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____3450 se =
        match uu____3450 with
        | (ses,exports,env,hidden) ->
            ((let uu____3480 =
                FStar_TypeChecker_Env.debug env FStar_Options.Low in
              if uu____3480
              then
                let _0_617 = FStar_Syntax_Print.sigelt_to_string se in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" _0_617
              else ());
             (let uu____3482 = tc_decl env se in
              match uu____3482 with
              | (ses',env,ses_elaborated) ->
                  ((let uu____3506 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LogTypes")) in
                    if uu____3506
                    then
                      let _0_620 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se  ->
                               let _0_619 =
                                 let _0_618 =
                                   FStar_Syntax_Print.sigelt_to_string se in
                                 Prims.strcat _0_618 "\n" in
                               Prims.strcat s _0_619) "" ses' in
                      FStar_Util.print1 "Checked: %s\n" _0_620
                    else ());
                   FStar_List.iter
                     (fun se  ->
                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env se) ses';
                   (let uu____3512 =
                      let accum_exports_hidden uu____3530 se =
                        match uu____3530 with
                        | (exports,hidden) ->
                            let uu____3546 = for_export hidden se in
                            (match uu____3546 with
                             | (se_exported,hidden) ->
                                 ((FStar_List.rev_append se_exported exports),
                                   hidden)) in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses' in
                    match uu____3512 with
                    | (exports,hidden) ->
                        (((FStar_List.rev_append ses' ses), exports, env,
                           hidden), ses_elaborated))))) in
      let uu____3596 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses in
      match uu____3596 with
      | (ses,exports,env,uu____3622) ->
          ((FStar_List.rev_append ses []),
            (FStar_List.rev_append exports []), env)
let tc_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
        FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____3647 = FStar_Options.debug_any () in
       if uu____3647
       then
         FStar_Util.print3 "%s %s of %s\n" action label
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
       let msg = Prims.strcat "Internals for " name in
       let env =
         let uu___99_3653 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___99_3653.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___99_3653.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___99_3653.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___99_3653.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___99_3653.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___99_3653.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___99_3653.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___99_3653.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___99_3653.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___99_3653.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___99_3653.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___99_3653.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___99_3653.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___99_3653.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___99_3653.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___99_3653.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___99_3653.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___99_3653.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___99_3653.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___99_3653.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___99_3653.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___99_3653.FStar_TypeChecker_Env.qname_and_index)
         } in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env =
          FStar_TypeChecker_Env.set_current_module env
            modul.FStar_Syntax_Syntax.name in
        let uu____3656 = tc_decls env modul.FStar_Syntax_Syntax.declarations in
        match uu____3656 with
        | (ses,exports,env) ->
            ((let uu___100_3674 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___100_3674.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___100_3674.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___100_3674.FStar_Syntax_Syntax.is_interface)
              }), exports, env)))
let tc_more_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul* FStar_Syntax_Syntax.sigelt Prims.list*
          FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____3690 = tc_decls env decls in
        match uu____3690 with
        | (ses,exports,env) ->
            let modul =
              let uu___101_3708 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___101_3708.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___101_3708.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___101_3708.FStar_Syntax_Syntax.is_interface)
              } in
            (modul, exports, env)
let check_exports:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env =
          let uu___102_3722 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___102_3722.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___102_3722.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___102_3722.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___102_3722.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___102_3722.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___102_3722.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___102_3722.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___102_3722.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___102_3722.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___102_3722.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___102_3722.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___102_3722.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___102_3722.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___102_3722.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___102_3722.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___102_3722.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___102_3722.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___102_3722.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___102_3722.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___102_3722.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___102_3722.FStar_TypeChecker_Env.qname_and_index)
          } in
        let check_term lid univs t =
          let uu____3733 = FStar_Syntax_Subst.open_univ_vars univs t in
          match uu____3733 with
          | (univs,t) ->
              ((let uu____3739 =
                  let _0_621 =
                    FStar_TypeChecker_Env.debug
                      (FStar_TypeChecker_Env.set_current_module env
                         modul.FStar_Syntax_Syntax.name) in
                  FStar_All.pipe_left _0_621 (FStar_Options.Other "Exports") in
                if uu____3739
                then
                  let _0_625 = FStar_Syntax_Print.lid_to_string lid in
                  let _0_624 =
                    let _0_622 =
                      FStar_All.pipe_right univs
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right _0_622 (FStar_String.concat ", ") in
                  let _0_623 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    _0_625 _0_624 _0_623
                else ());
               (let env = FStar_TypeChecker_Env.push_univ_vars env univs in
                let _0_626 = FStar_TypeChecker_TcTerm.tc_trivial_guard env t in
                FStar_All.pipe_right _0_626 Prims.ignore)) in
        let check_term lid univs t =
          FStar_Errors.message_prefix.FStar_Errors.set_prefix
            (let _0_628 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name in
             let _0_627 = FStar_Syntax_Print.lid_to_string lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               _0_628 _0_627);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt uu___81_3764 =
          match uu___81_3764 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____3767,uu____3768)
              ->
              let uu____3775 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private)) in
              if uu____3775
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs,binders,typ,uu____3783,uu____3784,uu____3785,r) ->
              let t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow
                      (let _0_629 = FStar_Syntax_Syntax.mk_Total typ in
                       (binders, _0_629)))) None r in
              check_term l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs,t,uu____3807,uu____3808,uu____3809,uu____3810,uu____3811)
              -> check_term l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs,t,quals,uu____3820)
              ->
              let uu____3823 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private)) in
              if uu____3823 then check_term l univs t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____3826,lbs),uu____3828,uu____3829,quals,uu____3831) ->
              let uu____3843 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private)) in
              if uu____3843
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs,binders,comp,quals,flags,r) ->
              let uu____3864 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private)) in
              if uu____3864
              then
                let arrow =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None r in
                check_term l univs arrow
              else ()
          | FStar_Syntax_Syntax.Sig_main _
            |FStar_Syntax_Syntax.Sig_assume _
             |FStar_Syntax_Syntax.Sig_new_effect _
              |FStar_Syntax_Syntax.Sig_new_effect_for_free _
               |FStar_Syntax_Syntax.Sig_sub_effect _
                |FStar_Syntax_Syntax.Sig_pragma _
              -> () in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
let finish_partial_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul =
          let uu___103_3897 = modul in
          {
            FStar_Syntax_Syntax.name =
              (uu___103_3897.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___103_3897.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          } in
        let env = FStar_TypeChecker_Env.finish_module env modul in
        (let uu____3900 = Prims.op_Negation (FStar_Options.lax ()) in
         if uu____3900 then check_exports env modul exports else ());
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env modul;
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____3906 = Prims.op_Negation (FStar_Options.interactive ()) in
         if uu____3906
         then
           let _0_630 = FStar_Options.restore_cmd_line_options true in
           FStar_All.pipe_right _0_630 Prims.ignore
         else ());
        (modul, env)
let tc_modul:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____3916 = tc_partial_modul env modul in
      match uu____3916 with
      | (modul,non_private_decls,env) ->
          finish_partial_modul env modul non_private_decls
let check_module:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul* FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____3937 = FStar_Options.debug_any () in
       if uu____3937
       then
         let _0_631 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           _0_631
       else ());
      (let env =
         let uu___104_3941 = env in
         let _0_632 =
           Prims.op_Negation
             (FStar_Options.should_verify
                (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
         {
           FStar_TypeChecker_Env.solver =
             (uu___104_3941.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___104_3941.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___104_3941.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___104_3941.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___104_3941.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___104_3941.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___104_3941.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___104_3941.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___104_3941.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___104_3941.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___104_3941.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___104_3941.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___104_3941.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___104_3941.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___104_3941.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___104_3941.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___104_3941.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___104_3941.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = _0_632;
           FStar_TypeChecker_Env.lax_universes =
             (uu___104_3941.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___104_3941.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___104_3941.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___104_3941.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___104_3941.FStar_TypeChecker_Env.qname_and_index)
         } in
       let uu____3942 = tc_modul env m in
       match uu____3942 with
       | (m,env) ->
           ((let uu____3950 =
               FStar_Options.dump_module
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
             if uu____3950
             then
               let _0_633 = FStar_Syntax_Print.modul_to_string m in
               FStar_Util.print1 "%s\n" _0_633
             else ());
            (let uu____3953 =
               (FStar_Options.dump_module
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize")) in
             if uu____3953
             then
               let normalize_toplevel_lets uu___82_3957 =
                 match uu___82_3957 with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),r,ids,qs,attrs) ->
                     let n =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
                     let update lb =
                       let uu____3984 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef in
                       match uu____3984 with
                       | (univnames,e) ->
                           let uu___105_3989 = lb in
                           let _0_635 =
                             let _0_634 =
                               FStar_TypeChecker_Env.push_univ_vars env
                                 univnames in
                             n _0_634 e in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___105_3989.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___105_3989.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___105_3989.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___105_3989.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = _0_635
                           } in
                     FStar_Syntax_Syntax.Sig_let
                       (let _0_637 =
                          let _0_636 = FStar_List.map update lbs in
                          (b, _0_636) in
                        (_0_637, r, ids, qs, attrs))
                 | se -> se in
               let normalized_module =
                 let uu___106_3999 = m in
                 let _0_638 =
                   FStar_List.map normalize_toplevel_lets
                     m.FStar_Syntax_Syntax.declarations in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___106_3999.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = _0_638;
                   FStar_Syntax_Syntax.exports =
                     (uu___106_3999.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___106_3999.FStar_Syntax_Syntax.is_interface)
                 } in
               let _0_639 =
                 FStar_Syntax_Print.modul_to_string normalized_module in
               FStar_Util.print1 "%s\n" _0_639
             else ());
            (m, env)))