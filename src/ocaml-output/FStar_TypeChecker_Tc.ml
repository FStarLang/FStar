open Prims
let set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun se  ->
      let uu____7 = FStar_Options.reuse_hint_for ()  in
      match uu____7 with
      | Some l ->
          let lid =
            let _0_261 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix _0_261 l  in
          let uu___84_11 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___84_11.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___84_11.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___84_11.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___84_11.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___84_11.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___84_11.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___84_11.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___84_11.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___84_11.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___84_11.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___84_11.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___84_11.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___84_11.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___84_11.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___84_11.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___84_11.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___84_11.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___84_11.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___84_11.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___84_11.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___84_11.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___84_11.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___84_11.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
      | None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let _0_264 = FStar_TypeChecker_Env.current_module env  in
                let _0_263 =
                  let _0_262 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right _0_262 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix _0_264 _0_263
            | l::uu____18 -> l  in
          let uu___85_20 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___85_20.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___85_20.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___85_20.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___85_20.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___85_20.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___85_20.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___85_20.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___85_20.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___85_20.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___85_20.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___85_20.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___85_20.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___85_20.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___85_20.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___85_20.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___85_20.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___85_20.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___85_20.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___85_20.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___85_20.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.type_of =
              (uu___85_20.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___85_20.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___85_20.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (Some (lid, (Prims.parse_int "0")))
          }
  
let log : FStar_TypeChecker_Env.env -> Prims.bool =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (Prims.op_Negation
         (let _0_265 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_265))
  
let tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____35 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____35 with
        | (t,c,g) ->
            (FStar_ST.write t.FStar_Syntax_Syntax.tk
               (Some
                  ((c.FStar_Syntax_Syntax.lcomp_res_typ).FStar_Syntax_Syntax.n));
             FStar_TypeChecker_Rel.force_trivial_guard env g;
             t)
  
let recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____57 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____57
         then
           let _0_266 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s _0_266
         else ());
        (let uu____59 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____59 with
         | (t',uu____64,uu____65) ->
             ((let uu____67 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____67
               then
                 let _0_267 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   _0_267
               else ());
              t))
  
let check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let _0_268 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env _0_268
  
let check_nogen env t k =
  let t = tc_check_trivial_guard env t k  in
  let _0_269 =
    FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Normalize.Beta]
      env t
     in
  ([], _0_269) 
let monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
          FStar_Syntax_Syntax.bv *
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____128 =
          Prims.raise
            (FStar_Errors.Error
               (let _0_270 =
                  FStar_TypeChecker_Err.unexpected_signature_for_monad env m
                    s
                   in
                (_0_270, (FStar_Ident.range_of_lid m))))
           in
        let s = FStar_Syntax_Subst.compress s  in
        match s.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs = FStar_Syntax_Subst.open_binders bs  in
            let n = FStar_List.length bs  in
            let uu____163 =
              if n < (Prims.parse_int "2")
              then ([], [])
              else FStar_Util.first_N (n - (Prims.parse_int "2")) bs  in
            (match uu____163 with
             | (indices,bs) ->
                 (match bs with
                  | (a,uu____230)::(wp,uu____232)::[] ->
                      (indices, a, (wp.FStar_Syntax_Syntax.sort))
                  | uu____244 -> fail ()))
        | uu____248 -> fail ()
  
let rec tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____311 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____311 with
      | (effect_params_un,signature_un,opening) ->
          let uu____318 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un  in
          (match uu____318 with
           | (effect_params,env,uu____324) ->
               let uu____325 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un
                  in
               (match uu____325 with
                | (signature,uu____329) ->
                    let ed =
                      let uu___86_331 = ed  in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___86_331.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___86_331.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___86_331.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___86_331.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___86_331.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___86_331.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___86_331.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___86_331.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___86_331.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___86_331.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___86_331.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___86_331.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___86_331.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___86_331.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___86_331.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___86_331.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___86_331.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___86_331.FStar_Syntax_Syntax.actions)
                      }  in
                    let ed =
                      match effect_params with
                      | [] -> ed
                      | uu____335 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts)
                               in
                            ([], t1)  in
                          let uu___87_353 = ed  in
                          let _0_286 = op ed.FStar_Syntax_Syntax.ret_wp  in
                          let _0_285 = op ed.FStar_Syntax_Syntax.bind_wp  in
                          let _0_284 = op ed.FStar_Syntax_Syntax.if_then_else
                             in
                          let _0_283 = op ed.FStar_Syntax_Syntax.ite_wp  in
                          let _0_282 = op ed.FStar_Syntax_Syntax.stronger  in
                          let _0_281 = op ed.FStar_Syntax_Syntax.close_wp  in
                          let _0_280 = op ed.FStar_Syntax_Syntax.assert_p  in
                          let _0_279 = op ed.FStar_Syntax_Syntax.assume_p  in
                          let _0_278 = op ed.FStar_Syntax_Syntax.null_wp  in
                          let _0_277 = op ed.FStar_Syntax_Syntax.trivial  in
                          let _0_276 =
                            Prims.snd
                              (op ([], (ed.FStar_Syntax_Syntax.repr)))
                             in
                          let _0_275 = op ed.FStar_Syntax_Syntax.return_repr
                             in
                          let _0_274 = op ed.FStar_Syntax_Syntax.bind_repr
                             in
                          let _0_273 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___88_357 = a  in
                                 let _0_272 =
                                   Prims.snd
                                     (op
                                        ([],
                                          (a.FStar_Syntax_Syntax.action_defn)))
                                    in
                                 let _0_271 =
                                   Prims.snd
                                     (op
                                        ([],
                                          (a.FStar_Syntax_Syntax.action_typ)))
                                    in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___88_357.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___88_357.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___88_357.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn = _0_272;
                                   FStar_Syntax_Syntax.action_typ = _0_271
                                 }) ed.FStar_Syntax_Syntax.actions
                             in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___87_353.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___87_353.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___87_353.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___87_353.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___87_353.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___87_353.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = _0_286;
                            FStar_Syntax_Syntax.bind_wp = _0_285;
                            FStar_Syntax_Syntax.if_then_else = _0_284;
                            FStar_Syntax_Syntax.ite_wp = _0_283;
                            FStar_Syntax_Syntax.stronger = _0_282;
                            FStar_Syntax_Syntax.close_wp = _0_281;
                            FStar_Syntax_Syntax.assert_p = _0_280;
                            FStar_Syntax_Syntax.assume_p = _0_279;
                            FStar_Syntax_Syntax.null_wp = _0_278;
                            FStar_Syntax_Syntax.trivial = _0_277;
                            FStar_Syntax_Syntax.repr = _0_276;
                            FStar_Syntax_Syntax.return_repr = _0_275;
                            FStar_Syntax_Syntax.bind_repr = _0_274;
                            FStar_Syntax_Syntax.actions = _0_273
                          }
                       in
                    let wp_with_fresh_result_type env mname signature =
                      let fail t =
                        Prims.raise
                          (FStar_Errors.Error
                             (let _0_287 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env mname t
                                 in
                              (_0_287, (FStar_Ident.range_of_lid mname))))
                         in
                      let uu____388 =
                        (FStar_Syntax_Subst.compress signature).FStar_Syntax_Syntax.n
                         in
                      match uu____388 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs = FStar_Syntax_Subst.open_binders bs  in
                          (match bs with
                           | (a,uu____411)::(wp,uu____413)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____422 -> fail signature)
                      | uu____423 -> fail signature  in
                    let uu____424 =
                      wp_with_fresh_result_type env
                        ed.FStar_Syntax_Syntax.mname
                        ed.FStar_Syntax_Syntax.signature
                       in
                    (match uu____424 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____442 =
                           let uu____443 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un
                              in
                           match uu____443 with
                           | (signature,uu____451) ->
                               wp_with_fresh_result_type env
                                 ed.FStar_Syntax_Syntax.mname signature
                            in
                         let env =
                           let _0_288 =
                             FStar_Syntax_Syntax.new_bv None
                               ed.FStar_Syntax_Syntax.signature
                              in
                           FStar_TypeChecker_Env.push_bv env _0_288  in
                         ((let uu____454 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED")
                              in
                           if uu____454
                           then
                             let _0_293 =
                               FStar_Syntax_Print.lid_to_string
                                 ed.FStar_Syntax_Syntax.mname
                                in
                             let _0_292 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed.FStar_Syntax_Syntax.binders
                                in
                             let _0_291 =
                               FStar_Syntax_Print.term_to_string
                                 ed.FStar_Syntax_Syntax.signature
                                in
                             let _0_290 =
                               FStar_Syntax_Print.term_to_string
                                 (FStar_Syntax_Syntax.bv_to_name a)
                                in
                             let _0_289 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort
                                in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               _0_293 _0_292 _0_291 _0_290 _0_289
                           else ());
                          (let check_and_gen' env uu____467 k =
                             match uu____467 with
                             | (uu____472,t) -> check_and_gen env t k  in
                           let return_wp =
                             let expected_k =
                               let _0_298 =
                                 let _0_296 = FStar_Syntax_Syntax.mk_binder a
                                    in
                                 let _0_295 =
                                   let _0_294 =
                                     FStar_Syntax_Syntax.null_binder
                                       (FStar_Syntax_Syntax.bv_to_name a)
                                      in
                                   [_0_294]  in
                                 _0_296 :: _0_295  in
                               let _0_297 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a  in
                               FStar_Syntax_Util.arrow _0_298 _0_297  in
                             check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp
                               expected_k
                              in
                           let bind_wp =
                             let uu____479 = fresh_effect_signature ()  in
                             match uu____479 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let _0_301 =
                                     let _0_299 =
                                       FStar_Syntax_Syntax.null_binder
                                         (FStar_Syntax_Syntax.bv_to_name a)
                                        in
                                     [_0_299]  in
                                   let _0_300 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow _0_301 _0_300  in
                                 let expected_k =
                                   let _0_312 =
                                     let _0_310 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range
                                        in
                                     let _0_309 =
                                       let _0_308 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let _0_307 =
                                         let _0_306 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let _0_305 =
                                           let _0_304 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a
                                              in
                                           let _0_303 =
                                             let _0_302 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b
                                                in
                                             [_0_302]  in
                                           _0_304 :: _0_303  in
                                         _0_306 :: _0_305  in
                                       _0_308 :: _0_307  in
                                     _0_310 :: _0_309  in
                                   let _0_311 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow _0_312 _0_311  in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.bind_wp expected_k
                              in
                           let if_then_else =
                             let p =
                               let _0_314 =
                                 let _0_313 = FStar_Syntax_Util.type_u ()  in
                                 FStar_All.pipe_right _0_313 Prims.fst  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname)) _0_314
                                in
                             let expected_k =
                               let _0_323 =
                                 let _0_321 = FStar_Syntax_Syntax.mk_binder a
                                    in
                                 let _0_320 =
                                   let _0_319 =
                                     FStar_Syntax_Syntax.mk_binder p  in
                                   let _0_318 =
                                     let _0_317 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     let _0_316 =
                                       let _0_315 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [_0_315]  in
                                     _0_317 :: _0_316  in
                                   _0_319 :: _0_318  in
                                 _0_321 :: _0_320  in
                               let _0_322 = FStar_Syntax_Syntax.mk_Total wp_a
                                  in
                               FStar_Syntax_Util.arrow _0_323 _0_322  in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.if_then_else expected_k
                              in
                           let ite_wp =
                             let expected_k =
                               let _0_328 =
                                 let _0_326 = FStar_Syntax_Syntax.mk_binder a
                                    in
                                 let _0_325 =
                                   let _0_324 =
                                     FStar_Syntax_Syntax.null_binder wp_a  in
                                   [_0_324]  in
                                 _0_326 :: _0_325  in
                               let _0_327 = FStar_Syntax_Syntax.mk_Total wp_a
                                  in
                               FStar_Syntax_Util.arrow _0_328 _0_327  in
                             check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp
                               expected_k
                              in
                           let stronger =
                             let uu____500 = FStar_Syntax_Util.type_u ()  in
                             match uu____500 with
                             | (t,uu____504) ->
                                 let expected_k =
                                   let _0_335 =
                                     let _0_333 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let _0_332 =
                                       let _0_331 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       let _0_330 =
                                         let _0_329 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a
                                            in
                                         [_0_329]  in
                                       _0_331 :: _0_330  in
                                     _0_333 :: _0_332  in
                                   let _0_334 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   FStar_Syntax_Util.arrow _0_335 _0_334  in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.stronger expected_k
                              in
                           let close_wp =
                             let b =
                               let _0_337 =
                                 let _0_336 = FStar_Syntax_Util.type_u ()  in
                                 FStar_All.pipe_right _0_336 Prims.fst  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname)) _0_337
                                in
                             let b_wp_a =
                               let _0_340 =
                                 let _0_338 =
                                   FStar_Syntax_Syntax.null_binder
                                     (FStar_Syntax_Syntax.bv_to_name b)
                                    in
                                 [_0_338]  in
                               let _0_339 = FStar_Syntax_Syntax.mk_Total wp_a
                                  in
                               FStar_Syntax_Util.arrow _0_340 _0_339  in
                             let expected_k =
                               let _0_347 =
                                 let _0_345 = FStar_Syntax_Syntax.mk_binder a
                                    in
                                 let _0_344 =
                                   let _0_343 =
                                     FStar_Syntax_Syntax.mk_binder b  in
                                   let _0_342 =
                                     let _0_341 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a
                                        in
                                     [_0_341]  in
                                   _0_343 :: _0_342  in
                                 _0_345 :: _0_344  in
                               let _0_346 = FStar_Syntax_Syntax.mk_Total wp_a
                                  in
                               FStar_Syntax_Util.arrow _0_347 _0_346  in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.close_wp expected_k
                              in
                           let assert_p =
                             let expected_k =
                               let _0_355 =
                                 let _0_353 = FStar_Syntax_Syntax.mk_binder a
                                    in
                                 let _0_352 =
                                   let _0_351 =
                                     FStar_Syntax_Syntax.null_binder
                                       (let _0_348 =
                                          FStar_Syntax_Util.type_u ()  in
                                        FStar_All.pipe_right _0_348 Prims.fst)
                                      in
                                   let _0_350 =
                                     let _0_349 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [_0_349]  in
                                   _0_351 :: _0_350  in
                                 _0_353 :: _0_352  in
                               let _0_354 = FStar_Syntax_Syntax.mk_Total wp_a
                                  in
                               FStar_Syntax_Util.arrow _0_355 _0_354  in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assert_p expected_k
                              in
                           let assume_p =
                             let expected_k =
                               let _0_363 =
                                 let _0_361 = FStar_Syntax_Syntax.mk_binder a
                                    in
                                 let _0_360 =
                                   let _0_359 =
                                     FStar_Syntax_Syntax.null_binder
                                       (let _0_356 =
                                          FStar_Syntax_Util.type_u ()  in
                                        FStar_All.pipe_right _0_356 Prims.fst)
                                      in
                                   let _0_358 =
                                     let _0_357 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [_0_357]  in
                                   _0_359 :: _0_358  in
                                 _0_361 :: _0_360  in
                               let _0_362 = FStar_Syntax_Syntax.mk_Total wp_a
                                  in
                               FStar_Syntax_Util.arrow _0_363 _0_362  in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.assume_p expected_k
                              in
                           let null_wp =
                             let expected_k =
                               let _0_366 =
                                 let _0_364 = FStar_Syntax_Syntax.mk_binder a
                                    in
                                 [_0_364]  in
                               let _0_365 = FStar_Syntax_Syntax.mk_Total wp_a
                                  in
                               FStar_Syntax_Util.arrow _0_366 _0_365  in
                             check_and_gen' env
                               ed.FStar_Syntax_Syntax.null_wp expected_k
                              in
                           let trivial_wp =
                             let uu____523 = FStar_Syntax_Util.type_u ()  in
                             match uu____523 with
                             | (t,uu____527) ->
                                 let expected_k =
                                   let _0_371 =
                                     let _0_369 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let _0_368 =
                                       let _0_367 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [_0_367]  in
                                     _0_369 :: _0_368  in
                                   let _0_370 =
                                     FStar_Syntax_Syntax.mk_GTotal t  in
                                   FStar_Syntax_Util.arrow _0_371 _0_370  in
                                 check_and_gen' env
                                   ed.FStar_Syntax_Syntax.trivial expected_k
                              in
                           let uu____529 =
                             let uu____535 =
                               (FStar_Syntax_Subst.compress
                                  ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                                in
                             match uu____535 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed.FStar_Syntax_Syntax.repr),
                                   (ed.FStar_Syntax_Syntax.bind_repr),
                                   (ed.FStar_Syntax_Syntax.return_repr),
                                   (ed.FStar_Syntax_Syntax.actions))
                             | uu____542 ->
                                 let repr =
                                   let uu____544 =
                                     FStar_Syntax_Util.type_u ()  in
                                   match uu____544 with
                                   | (t,uu____548) ->
                                       let expected_k =
                                         let _0_376 =
                                           let _0_374 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let _0_373 =
                                             let _0_372 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             [_0_372]  in
                                           _0_374 :: _0_373  in
                                         let _0_375 =
                                           FStar_Syntax_Syntax.mk_GTotal t
                                            in
                                         FStar_Syntax_Util.arrow _0_376
                                           _0_375
                                          in
                                       tc_check_trivial_guard env
                                         ed.FStar_Syntax_Syntax.repr
                                         expected_k
                                    in
                                 let mk_repr' t wp =
                                   let repr =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Normalize.EraseUniverses;
                                       FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                       env repr
                                      in
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (let _0_380 =
                                            let _0_379 =
                                              FStar_Syntax_Syntax.as_arg t
                                               in
                                            let _0_378 =
                                              let _0_377 =
                                                FStar_Syntax_Syntax.as_arg wp
                                                 in
                                              [_0_377]  in
                                            _0_379 :: _0_378  in
                                          (repr, _0_380)))) None
                                     FStar_Range.dummyRange
                                    in
                                 let mk_repr a wp =
                                   let _0_381 =
                                     FStar_Syntax_Syntax.bv_to_name a  in
                                   mk_repr' _0_381 wp  in
                                 let destruct_repr t =
                                   let uu____588 =
                                     (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                      in
                                   match uu____588 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____595,(t,uu____597)::(wp,uu____599)::[])
                                       -> (t, wp)
                                   | uu____633 ->
                                       failwith "Unexpected repr type"
                                    in
                                 let bind_repr =
                                   let r =
                                     let _0_382 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_All.pipe_right _0_382
                                       FStar_Syntax_Syntax.fv_to_tm
                                      in
                                   let uu____642 = fresh_effect_signature ()
                                      in
                                   match uu____642 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let _0_385 =
                                           let _0_383 =
                                             FStar_Syntax_Syntax.null_binder
                                               (FStar_Syntax_Syntax.bv_to_name
                                                  a)
                                              in
                                           [_0_383]  in
                                         let _0_384 =
                                           FStar_Syntax_Syntax.mk_Total wp_b
                                            in
                                         FStar_Syntax_Util.arrow _0_385
                                           _0_384
                                          in
                                       let wp_f =
                                         FStar_Syntax_Syntax.gen_bv "wp_f"
                                           None wp_a
                                          in
                                       let wp_g =
                                         FStar_Syntax_Syntax.gen_bv "wp_g"
                                           None a_wp_b
                                          in
                                       let x_a =
                                         let _0_386 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None _0_386
                                          in
                                       let wp_g_x =
                                         (let _0_390 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              wp_g
                                             in
                                          let _0_389 =
                                            let _0_388 =
                                              let _0_387 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x_a
                                                 in
                                              FStar_All.pipe_left
                                                FStar_Syntax_Syntax.as_arg
                                                _0_387
                                               in
                                            [_0_388]  in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            _0_390 _0_389) None
                                           FStar_Range.dummyRange
                                          in
                                       let res =
                                         let wp =
                                           (let _0_402 =
                                              let _0_391 =
                                                FStar_TypeChecker_Env.inst_tscheme
                                                  bind_wp
                                                 in
                                              FStar_All.pipe_right _0_391
                                                Prims.snd
                                               in
                                            let _0_401 =
                                              let _0_400 =
                                                let _0_399 =
                                                  let _0_398 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  let _0_397 =
                                                    let _0_396 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        b
                                                       in
                                                    let _0_395 =
                                                      let _0_394 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_f
                                                         in
                                                      let _0_393 =
                                                        let _0_392 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        [_0_392]  in
                                                      _0_394 :: _0_393  in
                                                    _0_396 :: _0_395  in
                                                  _0_398 :: _0_397  in
                                                r :: _0_399  in
                                              FStar_List.map
                                                FStar_Syntax_Syntax.as_arg
                                                _0_400
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              _0_402 _0_401) None
                                             FStar_Range.dummyRange
                                            in
                                         mk_repr b wp  in
                                       let expected_k =
                                         let _0_420 =
                                           let _0_418 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let _0_417 =
                                             let _0_416 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b
                                                in
                                             let _0_415 =
                                               let _0_414 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f
                                                  in
                                               let _0_413 =
                                                 let _0_412 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     (let _0_403 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_f
                                                         in
                                                      mk_repr a _0_403)
                                                    in
                                                 let _0_411 =
                                                   let _0_410 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g
                                                      in
                                                   let _0_409 =
                                                     let _0_408 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         (let _0_407 =
                                                            let _0_404 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                x_a
                                                               in
                                                            [_0_404]  in
                                                          let _0_406 =
                                                            let _0_405 =
                                                              mk_repr b
                                                                wp_g_x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.mk_Total
                                                              _0_405
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            _0_407 _0_406)
                                                        in
                                                     [_0_408]  in
                                                   _0_410 :: _0_409  in
                                                 _0_412 :: _0_411  in
                                               _0_414 :: _0_413  in
                                             _0_416 :: _0_415  in
                                           _0_418 :: _0_417  in
                                         let _0_419 =
                                           FStar_Syntax_Syntax.mk_Total res
                                            in
                                         FStar_Syntax_Util.arrow _0_420
                                           _0_419
                                          in
                                       let uu____677 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env expected_k
                                          in
                                       (match uu____677 with
                                        | (expected_k,uu____682,uu____683) ->
                                            let env =
                                              FStar_TypeChecker_Env.set_range
                                                env
                                                (Prims.snd
                                                   ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let env =
                                              let uu___89_687 = env  in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___89_687.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___89_687.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___89_687.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___89_687.FStar_TypeChecker_Env.qname_and_index)
                                              }  in
                                            let br =
                                              check_and_gen' env
                                                ed.FStar_Syntax_Syntax.bind_repr
                                                expected_k
                                               in
                                            br)
                                    in
                                 let return_repr =
                                   let x_a =
                                     let _0_421 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       _0_421
                                      in
                                   let res =
                                     let wp =
                                       (let _0_428 =
                                          let _0_422 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              return_wp
                                             in
                                          FStar_All.pipe_right _0_422
                                            Prims.snd
                                           in
                                        let _0_427 =
                                          let _0_426 =
                                            let _0_425 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            let _0_424 =
                                              let _0_423 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x_a
                                                 in
                                              [_0_423]  in
                                            _0_425 :: _0_424  in
                                          FStar_List.map
                                            FStar_Syntax_Syntax.as_arg _0_426
                                           in
                                        FStar_Syntax_Syntax.mk_Tm_app _0_428
                                          _0_427) None FStar_Range.dummyRange
                                        in
                                     mk_repr a wp  in
                                   let expected_k =
                                     let _0_433 =
                                       let _0_431 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let _0_430 =
                                         let _0_429 =
                                           FStar_Syntax_Syntax.mk_binder x_a
                                            in
                                         [_0_429]  in
                                       _0_431 :: _0_430  in
                                     let _0_432 =
                                       FStar_Syntax_Syntax.mk_Total res  in
                                     FStar_Syntax_Util.arrow _0_433 _0_432
                                      in
                                   let uu____707 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env expected_k
                                      in
                                   match uu____707 with
                                   | (expected_k,uu____715,uu____716) ->
                                       let env =
                                         FStar_TypeChecker_Env.set_range env
                                           (Prims.snd
                                              ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                          in
                                       let uu____719 =
                                         check_and_gen' env
                                           ed.FStar_Syntax_Syntax.return_repr
                                           expected_k
                                          in
                                       (match uu____719 with
                                        | (univs,repr) ->
                                            (match univs with
                                             | [] -> ([], repr)
                                             | uu____731 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr.FStar_Syntax_Syntax.pos)))))
                                    in
                                 let actions =
                                   let check_action act =
                                     let uu____742 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env
                                         act.FStar_Syntax_Syntax.action_typ
                                        in
                                     match uu____742 with
                                     | (act_typ,uu____747,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env act_typ
                                            in
                                         ((let uu____751 =
                                             FStar_TypeChecker_Env.debug env
                                               (FStar_Options.Other "ED")
                                              in
                                           if uu____751
                                           then
                                             let _0_435 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn
                                                in
                                             let _0_434 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ
                                                in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               _0_435 _0_434
                                           else ());
                                          (let uu____753 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn
                                              in
                                           match uu____753 with
                                           | (act_defn,uu____758,g_a) ->
                                               let act_defn =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant]
                                                   env act_defn
                                                  in
                                               let act_typ =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Normalize.UnfoldUntil
                                                      FStar_Syntax_Syntax.Delta_constant;
                                                   FStar_TypeChecker_Normalize.Eager_unfolding;
                                                   FStar_TypeChecker_Normalize.Beta]
                                                   env act_typ
                                                  in
                                               let uu____762 =
                                                 let act_typ =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ
                                                    in
                                                 match act_typ.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____780 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c
                                                        in
                                                     (match uu____780 with
                                                      | (bs,uu____786) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let k =
                                                            let _0_436 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res
                                                               in
                                                            FStar_Syntax_Util.arrow
                                                              bs _0_436
                                                             in
                                                          let uu____791 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env k
                                                             in
                                                          (match uu____791
                                                           with
                                                           | (k,uu____798,g)
                                                               -> (k, g)))
                                                 | uu____800 ->
                                                     Prims.raise
                                                       (FStar_Errors.Error
                                                          (let _0_439 =
                                                             let _0_438 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 act_typ
                                                                in
                                                             let _0_437 =
                                                               FStar_Syntax_Print.tag_of_term
                                                                 act_typ
                                                                in
                                                             FStar_Util.format2
                                                               "Actions must have function types (not: %s, a.k.a. %s)"
                                                               _0_438 _0_437
                                                              in
                                                           (_0_439,
                                                             (act_defn.FStar_Syntax_Syntax.pos))))
                                                  in
                                               (match uu____762 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env act_typ
                                                        expected_k
                                                       in
                                                    ((let _0_442 =
                                                        let _0_441 =
                                                          let _0_440 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g
                                                             in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k _0_440
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a _0_441
                                                         in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env _0_442);
                                                     (let act_typ =
                                                        let uu____808 =
                                                          (FStar_Syntax_Subst.compress
                                                             expected_k).FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____808 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____821 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____821
                                                             with
                                                             | (bs,c) ->
                                                                 let uu____826
                                                                   =
                                                                   destruct_repr
                                                                    (FStar_TypeChecker_Env.result_typ
                                                                    env c)
                                                                    in
                                                                 (match uu____826
                                                                  with
                                                                  | (a,wp) ->
                                                                    let c =
                                                                    let _0_448
                                                                    =
                                                                    let _0_443
                                                                    =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env a  in
                                                                    [_0_443]
                                                                     in
                                                                    let _0_447
                                                                    =
                                                                    let _0_446
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    a  in
                                                                    let _0_445
                                                                    =
                                                                    let _0_444
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [_0_444]
                                                                     in
                                                                    _0_446 ::
                                                                    _0_445
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_typ_name
                                                                    =
                                                                    (ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = _0_448;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = _0_447;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let _0_449
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs _0_449))
                                                        | uu____844 ->
                                                            failwith ""
                                                         in
                                                      let uu____845 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env act_defn
                                                         in
                                                      match uu____845 with
                                                      | (univs,act_defn) ->
                                                          let act_typ =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env act_typ
                                                             in
                                                          let uu___90_851 =
                                                            act  in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___90_851.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___90_851.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = univs;
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = act_typ
                                                          })))))
                                      in
                                   FStar_All.pipe_right
                                     ed.FStar_Syntax_Syntax.actions
                                     (FStar_List.map check_action)
                                    in
                                 (repr, bind_repr, return_repr, actions)
                              in
                           match uu____529 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 FStar_Syntax_Util.maybe_tot_arrow
                                   ed.FStar_Syntax_Syntax.binders
                                   ed.FStar_Syntax_Syntax.signature
                                  in
                               let uu____865 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t
                                  in
                               (match uu____865 with
                                | (univs,t) ->
                                    let signature =
                                      let uu____871 =
                                        let _0_450 =
                                          (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                           in
                                        (effect_params, _0_450)  in
                                      match uu____871 with
                                      | ([],uu____874) -> t
                                      | (uu____880,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____881,c)) ->
                                          FStar_TypeChecker_Env.result_typ
                                            env0 c
                                      | uu____893 -> failwith "Impossible"
                                       in
                                    let close n ts =
                                      let ts =
                                        let _0_451 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts
                                           in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs _0_451
                                         in
                                      let m =
                                        FStar_List.length (Prims.fst ts)  in
                                      (let uu____908 =
                                         ((n >= (Prims.parse_int "0")) &&
                                            (Prims.op_Negation
                                               (FStar_Syntax_Util.is_unknown
                                                  (Prims.snd ts))))
                                           && (m <> n)
                                          in
                                       if uu____908
                                       then
                                         let error =
                                           if m < n
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic"
                                            in
                                         failwith
                                           (let _0_453 =
                                              FStar_Util.string_of_int n  in
                                            let _0_452 =
                                              FStar_Syntax_Print.tscheme_to_string
                                                ts
                                               in
                                            FStar_Util.format3
                                              "The effect combinator is %s (n=%s) (%s)"
                                              error _0_453 _0_452)
                                       else ());
                                      ts  in
                                    let close_action act =
                                      let uu____922 =
                                        close (~- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn))
                                         in
                                      match uu____922 with
                                      | (univs,defn) ->
                                          let uu____927 =
                                            close (~- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ))
                                             in
                                          (match uu____927 with
                                           | (univs',typ) ->
                                               let uu___91_933 = act  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___91_933.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___91_933.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = univs;
                                                 FStar_Syntax_Syntax.action_defn
                                                   = defn;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = typ
                                               })
                                       in
                                    let nunivs = FStar_List.length univs  in
                                    let ed =
                                      let uu___92_938 = ed  in
                                      let _0_467 =
                                        close (Prims.parse_int "0") return_wp
                                         in
                                      let _0_466 =
                                        close (Prims.parse_int "1") bind_wp
                                         in
                                      let _0_465 =
                                        close (Prims.parse_int "0")
                                          if_then_else
                                         in
                                      let _0_464 =
                                        close (Prims.parse_int "0") ite_wp
                                         in
                                      let _0_463 =
                                        close (Prims.parse_int "0") stronger
                                         in
                                      let _0_462 =
                                        close (Prims.parse_int "1") close_wp
                                         in
                                      let _0_461 =
                                        close (Prims.parse_int "0") assert_p
                                         in
                                      let _0_460 =
                                        close (Prims.parse_int "0") assume_p
                                         in
                                      let _0_459 =
                                        close (Prims.parse_int "0") null_wp
                                         in
                                      let _0_458 =
                                        close (Prims.parse_int "0")
                                          trivial_wp
                                         in
                                      let _0_457 =
                                        Prims.snd
                                          (close (Prims.parse_int "0")
                                             ([], repr))
                                         in
                                      let _0_456 =
                                        close (Prims.parse_int "0")
                                          return_repr
                                         in
                                      let _0_455 =
                                        close (Prims.parse_int "1") bind_repr
                                         in
                                      let _0_454 =
                                        FStar_List.map close_action actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___92_938.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___92_938.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___92_938.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature;
                                        FStar_Syntax_Syntax.ret_wp = _0_467;
                                        FStar_Syntax_Syntax.bind_wp = _0_466;
                                        FStar_Syntax_Syntax.if_then_else =
                                          _0_465;
                                        FStar_Syntax_Syntax.ite_wp = _0_464;
                                        FStar_Syntax_Syntax.stronger = _0_463;
                                        FStar_Syntax_Syntax.close_wp = _0_462;
                                        FStar_Syntax_Syntax.assert_p = _0_461;
                                        FStar_Syntax_Syntax.assume_p = _0_460;
                                        FStar_Syntax_Syntax.null_wp = _0_459;
                                        FStar_Syntax_Syntax.trivial = _0_458;
                                        FStar_Syntax_Syntax.repr = _0_457;
                                        FStar_Syntax_Syntax.return_repr =
                                          _0_456;
                                        FStar_Syntax_Syntax.bind_repr =
                                          _0_455;
                                        FStar_Syntax_Syntax.actions = _0_454
                                      }  in
                                    ((let uu____942 =
                                        (FStar_TypeChecker_Env.debug env
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other "ED"))
                                         in
                                      if uu____942
                                      then
                                        FStar_Util.print_string
                                          (FStar_Syntax_Print.eff_decl_to_string
                                             false ed)
                                      else ());
                                     ed)))))))

and cps_and_elaborate :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt Prims.option)
  =
  fun env  ->
    fun ed  ->
      let uu____946 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____946 with
      | (effect_binders_un,signature_un) ->
          let uu____956 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____956 with
           | (effect_binders,env,uu____967) ->
               let uu____968 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un
                  in
               (match uu____968 with
                | (signature,uu____977) ->
                    let effect_binders =
                      FStar_List.map
                        (fun uu____986  ->
                           match uu____986 with
                           | (bv,qual) ->
                               let _0_469 =
                                 let uu___93_993 = bv  in
                                 let _0_468 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___93_993.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___93_993.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = _0_468
                                 }  in
                               (_0_469, qual)) effect_binders
                       in
                    let uu____994 =
                      let uu____999 =
                        (FStar_Syntax_Subst.compress signature_un).FStar_Syntax_Syntax.n
                         in
                      match uu____999 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1005)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1020 ->
                          failwith "bad shape for effect-for-free signature"
                       in
                    (match uu____994 with
                     | (a,effect_marker) ->
                         let a =
                           let uu____1037 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____1037
                           then
                             let _0_470 =
                               Some (FStar_Syntax_Syntax.range_of_bv a)  in
                             FStar_Syntax_Syntax.gen_bv "a" _0_470
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check t =
                           let subst =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders
                              in
                           let t = FStar_Syntax_Subst.subst subst t  in
                           let uu____1047 =
                             FStar_TypeChecker_TcTerm.tc_term env t  in
                           match uu____1047 with
                           | (t,comp,uu____1055) -> (t, comp)  in
                         let mk x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____1066 =
                           open_and_check ed.FStar_Syntax_Syntax.repr  in
                         (match uu____1066 with
                          | (repr,_comp) ->
                              ((let uu____1077 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____1077
                                then
                                  let _0_471 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    _0_471
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       FStar_Range.dummyRange)
                                   in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr
                                   in
                                let wp_type = recheck_debug "*" env wp_type
                                   in
                                let wp_a =
                                  let _0_476 =
                                    mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (let _0_475 =
                                            let _0_474 =
                                              let _0_473 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              let _0_472 =
                                                FStar_Syntax_Syntax.as_implicit
                                                  false
                                                 in
                                              (_0_473, _0_472)  in
                                            [_0_474]  in
                                          (wp_type, _0_475)))
                                     in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env
                                    _0_476
                                   in
                                let effect_signature =
                                  let binders =
                                    let _0_481 =
                                      let _0_477 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a, _0_477)  in
                                    let _0_480 =
                                      let _0_479 =
                                        let _0_478 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a
                                           in
                                        FStar_All.pipe_right _0_478
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [_0_479]  in
                                    _0_481 :: _0_480  in
                                  let binders =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders, effect_marker))
                                   in
                                let effect_signature =
                                  recheck_debug
                                    "turned into the effect signature" env
                                    effect_signature
                                   in
                                let sigelts = FStar_Util.mk_ref []  in
                                let mk_lid name =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       (Prims.strcat
                                          (FStar_Ident.text_of_lid
                                             ed.FStar_Syntax_Syntax.mname)
                                          (Prims.strcat "_" name)))
                                    FStar_Range.dummyRange
                                   in
                                let elaborate_and_star dmff_env item =
                                  let uu____1129 = item  in
                                  match uu____1129 with
                                  | (u_item,item) ->
                                      let uu____1141 = open_and_check item
                                         in
                                      (match uu____1141 with
                                       | (item,item_comp) ->
                                           ((let uu____1151 =
                                               Prims.op_Negation
                                                 (FStar_Syntax_Util.is_total_lcomp
                                                    item_comp)
                                                in
                                             if uu____1151
                                             then
                                               Prims.raise
                                                 (FStar_Errors.Err
                                                    (let _0_483 =
                                                       FStar_Syntax_Print.term_to_string
                                                         item
                                                        in
                                                     let _0_482 =
                                                       FStar_Syntax_Print.lcomp_to_string
                                                         item_comp
                                                        in
                                                     FStar_Util.format2
                                                       "Computation for [%s] is not total : %s !"
                                                       _0_483 _0_482))
                                             else ());
                                            (let uu____1153 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env item
                                                in
                                             match uu____1153 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let item_wp =
                                                   recheck_debug "*" env
                                                     item_wp
                                                    in
                                                 let item_elab =
                                                   recheck_debug "_" env
                                                     item_elab
                                                    in
                                                 (dmff_env, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____1166 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____1166 with
                                | (dmff_env,uu____1177,bind_wp,bind_elab) ->
                                    let uu____1180 =
                                      elaborate_and_star dmff_env
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____1180 with
                                     | (dmff_env,uu____1191,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1195 =
                                             (FStar_Syntax_Subst.compress
                                                return_wp).FStar_Syntax_Syntax.n
                                              in
                                           match uu____1195 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____1231 =
                                                 let uu____1239 =
                                                   let _0_484 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] _0_484
                                                    in
                                                 match uu____1239 with
                                                 | (b1::b2::[],body) ->
                                                     (b1, b2, body)
                                                 | uu____1280 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____1231 with
                                                | (b1,b2,body) ->
                                                    let env0 =
                                                      let _0_485 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        _0_485 [b1; b2]
                                                       in
                                                    let wp_b1 =
                                                      let _0_490 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_app
                                                             (let _0_489 =
                                                                let _0_488 =
                                                                  let _0_487
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (Prims.fst
                                                                    b1)  in
                                                                  let _0_486
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                  (_0_487,
                                                                    _0_486)
                                                                   in
                                                                [_0_488]  in
                                                              (wp_type,
                                                                _0_489)))
                                                         in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 _0_490
                                                       in
                                                    let uu____1316 =
                                                      let _0_492 =
                                                        let _0_491 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body _0_491
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        _0_492
                                                       in
                                                    (match uu____1316 with
                                                     | (bs,body,what') ->
                                                         let t2 =
                                                           (Prims.fst b2).FStar_Syntax_Syntax.sort
                                                            in
                                                         let pure_wp_type =
                                                           FStar_TypeChecker_DMFF.double_star
                                                             t2
                                                            in
                                                         let wp =
                                                           FStar_Syntax_Syntax.gen_bv
                                                             "wp" None
                                                             pure_wp_type
                                                            in
                                                         let body =
                                                           (let _0_496 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp
                                                               in
                                                            let _0_495 =
                                                              let _0_494 =
                                                                let _0_493 =
                                                                  FStar_Syntax_Util.abs
                                                                    [b2] body
                                                                    what'
                                                                   in
                                                                (_0_493,
                                                                  None)
                                                                 in
                                                              [_0_494]  in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              _0_496 _0_495)
                                                             None
                                                             FStar_Range.dummyRange
                                                            in
                                                         let _0_500 =
                                                           let _0_498 =
                                                             let _0_497 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp
                                                                in
                                                             [_0_497]  in
                                                           b1 :: _0_498  in
                                                         let _0_499 =
                                                           FStar_Syntax_Util.abs
                                                             bs body what
                                                            in
                                                         FStar_Syntax_Util.abs
                                                           _0_500 _0_499
                                                           (Some
                                                              (FStar_Util.Inr
                                                                 (FStar_Syntax_Const.effect_GTot_lid,
                                                                   [])))))
                                           | uu____1384 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let return_wp =
                                           let uu____1386 =
                                             (FStar_Syntax_Subst.compress
                                                return_wp).FStar_Syntax_Syntax.n
                                              in
                                           match uu____1386 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let _0_501 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] _0_501
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____1437 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let bind_wp =
                                           let uu____1439 =
                                             (FStar_Syntax_Subst.compress
                                                bind_wp).FStar_Syntax_Syntax.n
                                              in
                                           match uu____1439 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None
                                                  in
                                               let _0_504 =
                                                 let _0_503 =
                                                   let _0_502 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       (mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             r))
                                                      in
                                                   [_0_502]  in
                                                 FStar_List.append _0_503
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs _0_504
                                                 body what
                                           | uu____1466 ->
                                               failwith
                                                 "unexpected shape for bind"
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let _0_506 =
                                                mk
                                                  (FStar_Syntax_Syntax.Tm_app
                                                     (let _0_505 =
                                                        Prims.snd
                                                          (FStar_Syntax_Util.args_of_binders
                                                             effect_binders)
                                                         in
                                                      (t, _0_505)))
                                                 in
                                              FStar_Syntax_Subst.close
                                                effect_binders _0_506)
                                            in
                                         let register name item =
                                           let uu____1493 =
                                             let _0_508 = mk_lid name  in
                                             let _0_507 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders item None
                                                in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env _0_508 _0_507
                                              in
                                           match uu____1493 with
                                           | (sigelt,fv) ->
                                               ((let _0_510 =
                                                   let _0_509 =
                                                     FStar_ST.read sigelts
                                                      in
                                                   sigelt :: _0_509  in
                                                 FStar_ST.write sigelts
                                                   _0_510);
                                                fv)
                                            in
                                         let lift_from_pure_wp =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp =
                                           register "return_wp" return_wp  in
                                         ((let _0_512 =
                                             let _0_511 =
                                               FStar_ST.read sigelts  in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: _0_511
                                              in
                                           FStar_ST.write sigelts _0_512);
                                          (let return_elab =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let _0_514 =
                                              let _0_513 =
                                                FStar_ST.read sigelts  in
                                              (FStar_Syntax_Syntax.Sig_pragma
                                                 ((FStar_Syntax_Syntax.SetOptions
                                                     "--admit_smt_queries false"),
                                                   FStar_Range.dummyRange))
                                                :: _0_513
                                               in
                                            FStar_ST.write sigelts _0_514);
                                           (let bind_wp =
                                              register "bind_wp" bind_wp  in
                                            (let _0_516 =
                                               let _0_515 =
                                                 FStar_ST.read sigelts  in
                                               (FStar_Syntax_Syntax.Sig_pragma
                                                  ((FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"),
                                                    FStar_Range.dummyRange))
                                                 :: _0_515
                                                in
                                             FStar_ST.write sigelts _0_516);
                                            (let bind_elab =
                                               register "bind_elab" bind_elab
                                                in
                                             (let _0_518 =
                                                let _0_517 =
                                                  FStar_ST.read sigelts  in
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   ((FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries false"),
                                                     FStar_Range.dummyRange))
                                                  :: _0_517
                                                 in
                                              FStar_ST.write sigelts _0_518);
                                             (let uu____1543 =
                                                FStar_List.fold_left
                                                  (fun uu____1550  ->
                                                     fun action  ->
                                                       match uu____1550 with
                                                       | (dmff_env,actions)
                                                           ->
                                                           let uu____1562 =
                                                             elaborate_and_star
                                                               dmff_env
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn))
                                                              in
                                                           (match uu____1562
                                                            with
                                                            | (dmff_env,action_t,action_wp,action_elab)
                                                                ->
                                                                let name =
                                                                  ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
                                                                   in
                                                                let action_typ_with_wp
                                                                  =
                                                                  FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env
                                                                    action_t
                                                                    action_wp
                                                                   in
                                                                let action_elab
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab
                                                                   in
                                                                let action_typ_with_wp
                                                                  =
                                                                  register
                                                                    (
                                                                    Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp
                                                                   in
                                                                let _0_522 =
                                                                  let _0_521
                                                                    =
                                                                    let uu___94_1579
                                                                    = action
                                                                     in
                                                                    let _0_520
                                                                    =
                                                                    apply_close
                                                                    action_elab
                                                                     in
                                                                    let _0_519
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___94_1579.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___94_1579.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___94_1579.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    = _0_520;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    = _0_519
                                                                    }  in
                                                                  _0_521 ::
                                                                    actions
                                                                   in
                                                                (dmff_env,
                                                                  _0_522)))
                                                  (dmff_env, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____1543 with
                                              | (dmff_env,actions) ->
                                                  let actions =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a" None wp_a
                                                       in
                                                    let binders =
                                                      let _0_525 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let _0_524 =
                                                        let _0_523 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [_0_523]  in
                                                      _0_525 :: _0_524  in
                                                    let _0_532 =
                                                      let _0_531 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_app
                                                             (let _0_529 =
                                                                let _0_528 =
                                                                  let _0_527
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a  in
                                                                  let _0_526
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                  (_0_527,
                                                                    _0_526)
                                                                   in
                                                                [_0_528]  in
                                                              (repr, _0_529)))
                                                         in
                                                      let _0_530 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env _0_531
                                                        _0_530
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders _0_532 None
                                                     in
                                                  let repr =
                                                    recheck_debug "FC" env
                                                      repr
                                                     in
                                                  let repr =
                                                    register "repr" repr  in
                                                  let uu____1610 =
                                                    let uu____1613 =
                                                      (let _0_533 =
                                                         FStar_Syntax_Subst.compress
                                                           wp_type
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.unascribe
                                                         _0_533).FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1613 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow,uu____1619)
                                                        ->
                                                        let uu____1646 =
                                                          let uu____1655 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow
                                                             in
                                                          match uu____1655
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____1686 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____1646
                                                         with
                                                         | (type_param,effect_param,arrow)
                                                             ->
                                                             let uu____1712 =
                                                               (let _0_534 =
                                                                  FStar_Syntax_Subst.compress
                                                                    arrow
                                                                   in
                                                                FStar_All.pipe_left
                                                                  FStar_Syntax_Util.unascribe
                                                                  _0_534).FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____1712
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____1727
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____1727
                                                                   with
                                                                   | 
                                                                   (wp_binders,c)
                                                                    ->
                                                                    let uu____1734
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____1745
                                                                     ->
                                                                    match uu____1745
                                                                    with
                                                                    | 
                                                                    (bv,uu____1749)
                                                                    ->
                                                                    let _0_536
                                                                    =
                                                                    let _0_535
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    _0_535
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    _0_536
                                                                    Prims.op_Negation)
                                                                    wp_binders
                                                                     in
                                                                    (match uu____1734
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
                                                                    uu____1779
                                                                    ->
                                                                    failwith
                                                                    (let _0_537
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow  in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    _0_537)
                                                                     in
                                                                    let _0_539
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c  in
                                                                    let _0_538
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param
                                                                    ::
                                                                    effect_param)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None  in
                                                                    (_0_539,
                                                                    _0_538)))
                                                              | uu____1792 ->
                                                                  failwith
                                                                    (
                                                                    let _0_540
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow  in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    _0_540)))
                                                    | uu____1795 ->
                                                        failwith
                                                          (let _0_541 =
                                                             FStar_Syntax_Print.term_to_string
                                                               wp_type
                                                              in
                                                           FStar_Util.format1
                                                             "Impossible: pre/post abs %s"
                                                             _0_541)
                                                     in
                                                  (match uu____1610 with
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
                                                           let uu___95_1809 =
                                                             ed  in
                                                           let _0_552 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders
                                                              in
                                                           let _0_551 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders
                                                               effect_signature
                                                              in
                                                           let _0_550 =
                                                             let _0_542 =
                                                               apply_close
                                                                 return_wp
                                                                in
                                                             ([], _0_542)  in
                                                           let _0_549 =
                                                             let _0_543 =
                                                               apply_close
                                                                 bind_wp
                                                                in
                                                             ([], _0_543)  in
                                                           let _0_548 =
                                                             apply_close repr
                                                              in
                                                           let _0_547 =
                                                             let _0_544 =
                                                               apply_close
                                                                 return_elab
                                                                in
                                                             ([], _0_544)  in
                                                           let _0_546 =
                                                             let _0_545 =
                                                               apply_close
                                                                 bind_elab
                                                                in
                                                             ([], _0_545)  in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = _0_552;
                                                             FStar_Syntax_Syntax.signature
                                                               = _0_551;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = _0_550;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = _0_549;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___95_1809.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = _0_548;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = _0_547;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = _0_546;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions
                                                           }  in
                                                         let uu____1822 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env
                                                             effect_binders a
                                                             wp_a ed
                                                            in
                                                         match uu____1822
                                                         with
                                                         | (sigelts',ed) ->
                                                             ((let uu____1833
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____1833
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
                                                                    (Prims.parse_int "0")
                                                                 then
                                                                   let label_to_comp_typ
                                                                    l =
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_typ_name
                                                                    = l;
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    = [];
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    = [];
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                   let lift_from_pure
                                                                    =
                                                                    let _0_553
                                                                    =
                                                                    Some
                                                                    (apply_close
                                                                    lift_from_pure_wp)
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.sub_eff_univs
                                                                    = [];
                                                                    FStar_Syntax_Syntax.sub_eff_binders
                                                                    = [];
                                                                    FStar_Syntax_Syntax.sub_eff_source
                                                                    =
                                                                    (label_to_comp_typ
                                                                    FStar_Syntax_Const.effect_PURE_lid);
                                                                    FStar_Syntax_Syntax.sub_eff_target
                                                                    =
                                                                    (label_to_comp_typ
                                                                    ed.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.sub_eff_lift_wp
                                                                    = _0_553;
                                                                    FStar_Syntax_Syntax.sub_eff_lift
                                                                    = None
                                                                    }  in
                                                                   Some
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    (lift_from_pure,
                                                                    FStar_Range.dummyRange))
                                                                 else None
                                                                  in
                                                               let _0_555 =
                                                                 let _0_554 =
                                                                   FStar_List.rev
                                                                    (FStar_ST.read
                                                                    sigelts)
                                                                    in
                                                                 FStar_List.append
                                                                   _0_554
                                                                   sigelts'
                                                                  in
                                                               (_0_555, ed,
                                                                 lift_from_pure_opt))))))))))))))))))

and tc_lex_t :
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
              (lex_t,[],[],t,uu____1877,uu____1878,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top,[],_t_top,_lex_t_top,_0_556,[],uu____1883,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_557,[],uu____1888,r2))::[]
              when
              ((_0_556 = (Prims.parse_int "0")) &&
                 (_0_557 = (Prims.parse_int "0")))
                &&
                (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid)
                    &&
                    (FStar_Ident.lid_equals lex_top
                       FStar_Syntax_Const.lextop_lid))
                   &&
                   (FStar_Ident.lid_equals lex_cons
                      FStar_Syntax_Const.lexcons_lid))
              ->
              let u = FStar_Syntax_Syntax.new_univ_name (Some r)  in
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name u))
                  None r
                 in
              let t = FStar_Syntax_Subst.close_univ_vars [u] t  in
              let tc =
                FStar_Syntax_Syntax.Sig_inductive_typ
                  (lex_t, [u], [], t, [],
                    [FStar_Syntax_Const.lextop_lid;
                    FStar_Syntax_Const.lexcons_lid], [], r)
                 in
              let utop = FStar_Syntax_Syntax.new_univ_name (Some r1)  in
              let lex_top_t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_uinst
                      (let _0_558 =
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              FStar_Syntax_Const.lex_t_lid r1)
                           FStar_Syntax_Syntax.Delta_constant None
                          in
                       (_0_558, [FStar_Syntax_Syntax.U_name utop])))) None r1
                 in
              let lex_top_t =
                FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
              let dc_lextop =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_top, [utop], lex_top_t, FStar_Syntax_Const.lex_t_lid,
                    (Prims.parse_int "0"), [], [], r1)
                 in
              let ucons1 = FStar_Syntax_Syntax.new_univ_name (Some r2)  in
              let ucons2 = FStar_Syntax_Syntax.new_univ_name (Some r2)  in
              let lex_cons_t =
                let a =
                  let _0_559 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2
                     in
                  FStar_Syntax_Syntax.new_bv (Some r2) _0_559  in
                let hd =
                  let _0_560 = FStar_Syntax_Syntax.bv_to_name a  in
                  FStar_Syntax_Syntax.new_bv (Some r2) _0_560  in
                let tl =
                  let _0_562 =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_uinst
                          (let _0_561 =
                             FStar_Syntax_Syntax.fvar
                               (FStar_Ident.set_lid_range
                                  FStar_Syntax_Const.lex_t_lid r2)
                               FStar_Syntax_Syntax.Delta_constant None
                              in
                           (_0_561, [FStar_Syntax_Syntax.U_name ucons2]))))
                      None r2
                     in
                  FStar_Syntax_Syntax.new_bv (Some r2) _0_562  in
                let res =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uinst
                        (let _0_563 =
                           FStar_Syntax_Syntax.fvar
                             (FStar_Ident.set_lid_range
                                FStar_Syntax_Const.lex_t_lid r2)
                             FStar_Syntax_Syntax.Delta_constant None
                            in
                         (_0_563,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])))) None r2
                   in
                let _0_564 = FStar_Syntax_Syntax.mk_Total res  in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd, None);
                  (tl, None)] _0_564
                 in
              let lex_cons_t =
                FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                  lex_cons_t
                 in
              let dc_lexcons =
                FStar_Syntax_Syntax.Sig_datacon
                  (lex_cons, [ucons1; ucons2], lex_cons_t,
                    FStar_Syntax_Const.lex_t_lid, (Prims.parse_int "0"), [],
                    [], r2)
                 in
              FStar_Syntax_Syntax.Sig_bundle
                (let _0_565 = FStar_TypeChecker_Env.get_range env  in
                 ([tc; dc_lextop; dc_lexcons], [], lids, _0_565))
          | uu____2008 ->
              failwith
                (let _0_566 =
                   FStar_Syntax_Print.sigelt_to_string
                     (FStar_Syntax_Syntax.Sig_bundle
                        (ses, [], lids, FStar_Range.dummyRange))
                    in
                 FStar_Util.format1 "Unexpected lex_t: %s\n" _0_566)

and tc_assume :
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
            let env = FStar_TypeChecker_Env.set_range env r  in
            let uu____2020 = FStar_Syntax_Util.type_u ()  in
            match uu____2020 with
            | (k,uu____2024) ->
                let phi =
                  let _0_567 = tc_check_trivial_guard env phi k  in
                  FStar_All.pipe_right _0_567
                    (FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Eager_unfolding] env)
                   in
                (FStar_TypeChecker_Util.check_uvars r phi;
                 FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r))

and tc_inductive :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
            Prims.list)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env0 = env  in
          let uu____2036 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids
             in
          match uu____2036 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let _0_568 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas
                   in
                FStar_All.pipe_right _0_568 FStar_List.flatten  in
              ((let uu____2060 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____2060
                then ()
                else
                  (let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   FStar_List.iter
                     (fun ty  ->
                        let b =
                          FStar_TypeChecker_TcInductive.check_positivity ty
                            env
                           in
                        if Prims.op_Negation b
                        then
                          let uu____2066 =
                            match ty with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____2072,uu____2073,uu____2074,uu____2075,uu____2076,uu____2077,r)
                                -> (lid, r)
                            | uu____2085 -> failwith "Impossible!"  in
                          match uu____2066 with
                          | (lid,r) ->
                              FStar_Errors.report r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____2094 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____2098,uu____2099,uu____2100,uu____2101,uu____2102,uu____2103,uu____2104)
                        -> lid
                    | uu____2111 -> failwith "Impossible"  in
                  let types_to_skip =
                    ["c_False";
                    "c_True";
                    "equals";
                    "h_equals";
                    "c_and";
                    "c_or"]  in
                  FStar_List.existsb
                    (fun s  -> s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                    types_to_skip
                   in
                let is_noeq =
                  FStar_List.existsb (fun q  -> q = FStar_Syntax_Syntax.Noeq)
                    quals
                   in
                let uu____2117 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq
                   in
                if uu____2117
                then ([sig_bndle], data_ops_ses)
                else
                  (let is_unopteq =
                     FStar_List.existsb
                       (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals
                      in
                   let ses =
                     if is_unopteq
                     then
                       FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                     else
                       FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                         sig_bndle tcs datas env0 tc_assume
                      in
                   let _0_571 =
                     let _0_570 =
                       FStar_Syntax_Syntax.Sig_bundle
                         (let _0_569 = FStar_TypeChecker_Env.get_range env0
                             in
                          ((FStar_List.append tcs datas), quals, lids,
                            _0_569))
                        in
                     _0_570 :: ses  in
                   (_0_571, data_ops_ses))))

and tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun se  ->
      let env = set_hint_correlator env se  in
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
           let env = FStar_TypeChecker_Env.set_range env r  in
           let se = tc_lex_t env ses quals lids  in
           let _0_572 = FStar_TypeChecker_Env.push_sigelt env se  in
           ([se], _0_572, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env = FStar_TypeChecker_Env.set_range env r  in
           let uu____2185 = tc_inductive env ses quals lids  in
           (match uu____2185 with
            | (ses,projectors_ses) ->
                let env =
                  FStar_List.fold_left
                    (fun env'  ->
                       fun se  -> FStar_TypeChecker_Env.push_sigelt env' se)
                    env ses
                   in
                (ses, env, projectors_ses))
       | FStar_Syntax_Syntax.Sig_pragma (p,r) ->
           let set_options t s =
             let uu____2215 = FStar_Options.set_options t s  in
             match uu____2215 with
             | FStar_Getopt.Success  -> ()
             | FStar_Getopt.Help  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ("Failed to process pragma: use 'fstar --help' to see which options are available",
                        r))
             | FStar_Getopt.Error s ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Failed to process pragma: " s), r))
              in
           (match p with
            | FStar_Syntax_Syntax.LightOff  ->
                (if p = FStar_Syntax_Syntax.LightOff
                 then FStar_Options.set_ml_ish ()
                 else ();
                 ([se], env, []))
            | FStar_Syntax_Syntax.SetOptions o ->
                (set_options FStar_Options.Set o; ([se], env, []))
            | FStar_Syntax_Syntax.ResetOptions sopt ->
                ((let _0_573 = FStar_Options.restore_cmd_line_options false
                     in
                  FStar_All.pipe_right _0_573 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options FStar_Options.Reset s);
                 (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
           let uu____2240 = cps_and_elaborate env ne  in
           (match uu____2240 with
            | (ses,ne,lift_from_pure_opt) ->
                let effect_and_lift_ses =
                  match lift_from_pure_opt with
                  | Some lift ->
                      [FStar_Syntax_Syntax.Sig_new_effect (ne, r); lift]
                  | None  -> [FStar_Syntax_Syntax.Sig_new_effect (ne, r)]  in
                ([], env, (FStar_List.append ses effect_and_lift_ses)))
       | FStar_Syntax_Syntax.Sig_new_effect (ne,r) ->
           let ne = tc_eff_decl env ne  in
           Printf.printf "Definining effect %s\n" (FStar_Ident.text_of_lid ne.mname);
           let se = FStar_Syntax_Syntax.Sig_new_effect (ne, r)  in
           let env = FStar_TypeChecker_Env.push_sigelt env se  in
           let uu____2269 =
             FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____2280  ->
                     fun a  ->
                       match uu____2280 with
                       | (env,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne.FStar_Syntax_Syntax.mname a
                              in
                           let _0_574 =
                             FStar_TypeChecker_Env.push_sigelt env se_let  in
                           (_0_574, (se_let :: ses))) (env, [se]))
              in
           (match uu____2269 with
            | (env,ses) ->
                let env = FStar_TypeChecker_Util.build_lattice env se  in
                ([se], env, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub,r) ->
           let source =
             (sub.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name
              in
           let target =
             (sub.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name
              in
           Printf.printf "Definining sub-effect %s ~> %s\n" (FStar_Ident.text_of_lid source) (FStar_Ident.text_of_lid target);
           let ed_src = FStar_TypeChecker_Env.get_effect_decl env source  in
           let ed_tgt = FStar_TypeChecker_Env.get_effect_decl env target  in
           let uu____2313 =
             let _0_575 = FStar_TypeChecker_Env.lookup_effect_lid env source
                in
             monad_signature env source _0_575  in
           (match uu____2313 with
            | (indices_a,a,wp_a_src) ->
                let uu____2340 =
                  let _0_576 =
                    FStar_TypeChecker_Env.lookup_effect_lid env target  in
                  monad_signature env target _0_576  in
                (match uu____2340 with
                 | (indices_b,b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let _0_579 =
                         let _0_578 =
                           FStar_Syntax_Syntax.NT
                             (let _0_577 = FStar_Syntax_Syntax.bv_to_name a
                                 in
                              (b, _0_577))
                            in
                         [_0_578]  in
                       FStar_Syntax_Subst.subst _0_579 wp_b_tgt  in
                     let expected_k =
                       let _0_584 =
                         let _0_582 = FStar_Syntax_Syntax.mk_binder a  in
                         let _0_581 =
                           let _0_580 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [_0_580]  in
                         _0_582 :: _0_581  in
                       let _0_583 = FStar_Syntax_Syntax.mk_Total wp_a_tgt  in
                       FStar_Syntax_Util.arrow _0_584 _0_583  in
                     let repr_type eff_name a wp =
                       let no_reify l =
                         Prims.raise
                           (FStar_Errors.Error
                              (let _0_586 =
                                 FStar_Util.format1
                                   "Effect %s cannot be reified"
                                   l.FStar_Ident.str
                                  in
                               let _0_585 =
                                 FStar_TypeChecker_Env.get_range env  in
                               (_0_586, _0_585)))
                          in
                       let uu____2389 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____2389 with
                       | None  -> no_reify eff_name
                       | Some ed ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ([], (ed.FStar_Syntax_Syntax.repr))
                              in
                           let uu____2396 =
                             Prims.op_Negation
                               (FStar_All.pipe_right
                                  ed.FStar_Syntax_Syntax.qualifiers
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Reifiable))
                              in
                           if uu____2396
                           then no_reify eff_name
                           else
                             (let _0_591 =
                                FStar_TypeChecker_Env.get_range env  in
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (let _0_590 =
                                       let _0_589 =
                                         FStar_Syntax_Syntax.as_arg a  in
                                       let _0_588 =
                                         let _0_587 =
                                           FStar_Syntax_Syntax.as_arg wp  in
                                         [_0_587]  in
                                       _0_589 :: _0_588  in
                                     (repr, _0_590)))) None _0_591)
                        in
                     let uu____2410 =
                       match ((sub.FStar_Syntax_Syntax.sub_eff_lift),
                               (sub.FStar_Syntax_Syntax.sub_eff_lift_wp))
                       with
                       | (None ,None ) -> failwith "Impossible"
                       | (lift,Some lift_wp) ->
                           let _0_592 =
                             tc_check_trivial_guard env lift_wp expected_k
                              in
                           (lift, _0_592)
                       | (Some lift,None ) ->
                           let dmff_env =
                             FStar_TypeChecker_DMFF.empty env
                               (FStar_TypeChecker_TcTerm.tc_constant
                                  FStar_Range.dummyRange)
                              in
                           let uu____2434 =
                             FStar_TypeChecker_DMFF.star_expr dmff_env lift
                              in
                           (match uu____2434 with
                            | (uu____2441,lift_wp,lift_elab) ->
                                let uu____2444 =
                                  recheck_debug "lift-wp" env lift_wp  in
                                let uu____2445 =
                                  recheck_debug "lift-elab" env lift_elab  in
                                ((Some lift_elab), lift_wp))
                        in
                     (match uu____2410 with
                      | (lift,lift_wp) ->
                          let lax = env.FStar_TypeChecker_Env.lax  in
                          let env =
                            let uu___96_2458 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___96_2458.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___96_2458.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___96_2458.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___96_2458.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___96_2458.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___96_2458.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___96_2458.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___96_2458.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___96_2458.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___96_2458.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___96_2458.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___96_2458.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___96_2458.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___96_2458.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___96_2458.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___96_2458.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___96_2458.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___96_2458.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___96_2458.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___96_2458.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___96_2458.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___96_2458.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___96_2458.FStar_TypeChecker_Env.qname_and_index)
                            }  in
                          let lift =
                            match lift with
                            | None  -> None
                            | Some lift ->
                                let source =
                                  (sub.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name
                                   in
                                let uu____2464 =
                                  let _0_593 =
                                    FStar_TypeChecker_Env.lookup_effect_lid
                                      env source
                                     in
                                  monad_signature env source _0_593  in
                                (match uu____2464 with
                                 | (indices_a,a,wp_a_src) ->
                                     let wp_a =
                                       FStar_Syntax_Syntax.new_bv None
                                         wp_a_src
                                        in
                                     let a_typ =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     let wp_a_typ =
                                       FStar_Syntax_Syntax.bv_to_name wp_a
                                        in
                                     let repr_f =
                                       repr_type source a_typ wp_a_typ  in
                                     let repr_result =
                                       let lift_wp =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.EraseUniverses;
                                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                                           env lift_wp
                                          in
                                       let lift_wp_a =
                                         let _0_598 =
                                           FStar_TypeChecker_Env.get_range
                                             env
                                            in
                                         (FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (let _0_597 =
                                                  let _0_596 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      a_typ
                                                     in
                                                  let _0_595 =
                                                    let _0_594 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp_a_typ
                                                       in
                                                    [_0_594]  in
                                                  _0_596 :: _0_595  in
                                                (lift_wp, _0_597)))) None
                                           _0_598
                                          in
                                       let target =
                                         (sub.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name
                                          in
                                       repr_type target a_typ lift_wp_a  in
                                     let expected_k =
                                       let _0_605 =
                                         let _0_603 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let _0_602 =
                                           let _0_601 =
                                             FStar_Syntax_Syntax.mk_binder
                                               wp_a
                                              in
                                           let _0_600 =
                                             let _0_599 =
                                               FStar_Syntax_Syntax.null_binder
                                                 repr_f
                                                in
                                             [_0_599]  in
                                           _0_601 :: _0_600  in
                                         _0_603 :: _0_602  in
                                       let _0_604 =
                                         FStar_Syntax_Syntax.mk_Total
                                           repr_result
                                          in
                                       FStar_Syntax_Util.arrow _0_605 _0_604
                                        in
                                     let uu____2511 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env expected_k
                                        in
                                     (match uu____2511 with
                                      | (expected_k,uu____2517,uu____2518) ->
                                          let lift =
                                            tc_check_trivial_guard env lift
                                              expected_k
                                             in
                                          Some lift))
                             in
                          let env =
                            let uu___97_2521 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___97_2521.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___97_2521.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___97_2521.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___97_2521.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___97_2521.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___97_2521.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___97_2521.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___97_2521.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___97_2521.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___97_2521.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___97_2521.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___97_2521.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___97_2521.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___97_2521.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___97_2521.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___97_2521.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___97_2521.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___97_2521.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = lax;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___97_2521.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___97_2521.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___97_2521.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___97_2521.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___97_2521.FStar_TypeChecker_Env.qname_and_index)
                            }  in
                          let sub =
                            let uu___98_2523 = sub  in
                            {
                              FStar_Syntax_Syntax.sub_eff_univs =
                                (uu___98_2523.FStar_Syntax_Syntax.sub_eff_univs);
                              FStar_Syntax_Syntax.sub_eff_binders =
                                (uu___98_2523.FStar_Syntax_Syntax.sub_eff_binders);
                              FStar_Syntax_Syntax.sub_eff_source =
                                (uu___98_2523.FStar_Syntax_Syntax.sub_eff_source);
                              FStar_Syntax_Syntax.sub_eff_target =
                                (uu___98_2523.FStar_Syntax_Syntax.sub_eff_target);
                              FStar_Syntax_Syntax.sub_eff_lift_wp =
                                (Some lift_wp);
                              FStar_Syntax_Syntax.sub_eff_lift = lift
                            }  in
                          let se =
                            FStar_Syntax_Syntax.Sig_sub_effect (sub, r)  in
                          let env = FStar_TypeChecker_Env.push_sigelt env se
                             in
                          let env =
                            FStar_TypeChecker_Util.build_lattice env se  in
                          ([se], env, []))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env  in
           let env = FStar_TypeChecker_Env.set_range env r  in
           let uu____2543 = FStar_Syntax_Subst.open_comp tps c  in
           (match uu____2543 with
            | (tps,c) ->
                let uu____2553 = FStar_TypeChecker_TcTerm.tc_tparams env tps
                   in
                (match uu____2553 with
                 | (tps,env,us) ->
                     let uu____2565 = FStar_TypeChecker_TcTerm.tc_comp env c
                        in
                     (match uu____2565 with
                      | (c,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env g;
                           (let tps = FStar_Syntax_Subst.close_binders tps
                               in
                            let c = FStar_Syntax_Subst.close_comp tps c  in
                            let uu____2580 =
                              let _0_606 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                                  None r
                                 in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 _0_606
                               in
                            match uu____2580 with
                            | (uvs,t) ->
                                let uu____2598 =
                                  let uu____2606 =
                                    let _0_607 =
                                      (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                                       in
                                    (tps, _0_607)  in
                                  match uu____2606 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____2616,c)) -> ([], c)
                                  | (uu____2640,FStar_Syntax_Syntax.Tm_arrow
                                     (tps,c)) -> (tps, c)
                                  | uu____2658 -> failwith "Impossible"  in
                                (match uu____2598 with
                                 | (tps,c) ->
                                     (if
                                        ((FStar_List.length uvs) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____2688 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs t
                                            in
                                         match uu____2688 with
                                         | (uu____2691,t) ->
                                             Prims.raise
                                               (FStar_Errors.Error
                                                  (let _0_611 =
                                                     let _0_610 =
                                                       FStar_Syntax_Print.lid_to_string
                                                         lid
                                                        in
                                                     let _0_609 =
                                                       FStar_All.pipe_right
                                                         (FStar_List.length
                                                            uvs)
                                                         FStar_Util.string_of_int
                                                        in
                                                     let _0_608 =
                                                       FStar_Syntax_Print.term_to_string
                                                         t
                                                        in
                                                     FStar_Util.format3
                                                       "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                       _0_610 _0_609 _0_608
                                                      in
                                                   (_0_611, r))))
                                      else ();
                                      (let se =
                                         FStar_Syntax_Syntax.Sig_effect_abbrev
                                           (lid, uvs, tps, c, tags, flags, r)
                                          in
                                       let env =
                                         FStar_TypeChecker_Env.push_sigelt
                                           env0 se
                                          in
                                       ([se], env, [])))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals,_)
         |FStar_Syntax_Syntax.Sig_let (_,_,_,quals,_) when
           FStar_All.pipe_right quals
             (FStar_Util.for_some
                (fun uu___78_2724  ->
                   match uu___78_2724 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____2725 -> false))
           -> ([], env, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env = FStar_TypeChecker_Env.set_range env r  in
           let uu____2736 =
             if uvs = []
             then
               let _0_612 = Prims.fst (FStar_Syntax_Util.type_u ())  in
               check_and_gen env t _0_612
             else
               (let uu____2738 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                match uu____2738 with
                | (uvs,t) ->
                    let t =
                      let _0_613 = Prims.fst (FStar_Syntax_Util.type_u ())
                         in
                      tc_check_trivial_guard env t _0_613  in
                    let t =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env t
                       in
                    let _0_614 = FStar_Syntax_Subst.close_univ_vars uvs t  in
                    (uvs, _0_614))
              in
           (match uu____2736 with
            | (uvs,t) ->
                let se =
                  FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r)
                   in
                let env = FStar_TypeChecker_Env.push_sigelt env se  in
                ([se], env, []))
       | FStar_Syntax_Syntax.Sig_assume (lid,phi,quals,r) ->
           let se = tc_assume env lid phi quals r  in
           let env = FStar_TypeChecker_Env.push_sigelt env se  in
           ([se], env, [])
       | FStar_Syntax_Syntax.Sig_main (e,r) ->
           let env = FStar_TypeChecker_Env.set_range env r  in
           let env =
             FStar_TypeChecker_Env.set_expected_typ env
               FStar_TypeChecker_Common.t_unit
              in
           let uu____2774 = FStar_TypeChecker_TcTerm.tc_term env e  in
           (match uu____2774 with
            | (e,c,g1) ->
                let uu____2786 =
                  let _0_617 =
                    Some
                      (FStar_Syntax_Util.ml_comp
                         FStar_TypeChecker_Common.t_unit r)
                     in
                  let _0_616 =
                    let _0_615 = c.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                    (e, _0_615)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env _0_617
                    _0_616
                   in
                (match uu____2786 with
                 | (e,uu____2798,g) ->
                     ((let _0_618 = FStar_TypeChecker_Rel.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env _0_618);
                      (let se = FStar_Syntax_Syntax.Sig_main (e, r)  in
                       let env = FStar_TypeChecker_Env.push_sigelt env se  in
                       ([se], env, [])))))
       | FStar_Syntax_Syntax.Sig_let (lbs,r,lids,quals,attrs) ->
           let env = FStar_TypeChecker_Env.set_range env r  in
           let check_quals_eq l qopt q =
             match qopt with
             | None  -> Some q
             | Some q' ->
                 let uu____2842 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____2842
                 then Some q
                 else
                   Prims.raise
                     (FStar_Errors.Error
                        (let _0_622 =
                           let _0_621 = FStar_Syntax_Print.lid_to_string l
                              in
                           let _0_620 = FStar_Syntax_Print.quals_to_string q
                              in
                           let _0_619 = FStar_Syntax_Print.quals_to_string q'
                              in
                           FStar_Util.format3
                             "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                             _0_621 _0_620 _0_619
                            in
                         (_0_622, r)))
              in
           let uu____2853 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____2874  ->
                     fun lb  ->
                       match uu____2874 with
                       | (gen,lbs,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____2898 =
                             let uu____2904 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____2904 with
                             | None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen, lb, quals_opt)
                             | Some ((uvs,tval),quals) ->
                                 let quals_opt =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals
                                    in
                                 ((match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  -> ()
                                   | uu____2956 ->
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
                                  (let _0_623 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef))
                                      in
                                   (false, _0_623, quals_opt)))
                              in
                           (match uu____2898 with
                            | (gen,lb,quals_opt) ->
                                (gen, (lb :: lbs), quals_opt)))
                  (true, [], (if quals = [] then None else Some quals)))
              in
           (match uu____2853 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3017 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___79_3019  ->
                                match uu___79_3019 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3020 -> false))
                         in
                      if uu____3017
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs' = FStar_List.rev lbs'  in
                let e =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_let
                        (let _0_624 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_constant
                                FStar_Const.Const_unit) None r
                            in
                         (((Prims.fst lbs), lbs'), _0_624)))) None r
                   in
                let uu____3051 =
                  let uu____3057 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___99_3061 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___99_3061.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___99_3061.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___99_3061.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___99_3061.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___99_3061.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___99_3061.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___99_3061.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___99_3061.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___99_3061.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___99_3061.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___99_3061.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___99_3061.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___99_3061.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___99_3061.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___99_3061.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___99_3061.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___99_3061.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___99_3061.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___99_3061.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___99_3061.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___99_3061.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___99_3061.FStar_TypeChecker_Env.qname_and_index)
                       }) e
                     in
                  match uu____3057 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs,e);
                       FStar_Syntax_Syntax.tk = uu____3069;
                       FStar_Syntax_Syntax.pos = uu____3070;
                       FStar_Syntax_Syntax.vars = uu____3071;_},uu____3072,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals =
                        match e.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3091,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals
                        | uu____3096 -> quals  in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs, r, lids, quals, attrs)), lbs)
                  | uu____3106 -> failwith "impossible"  in
                (match uu____3051 with
                 | (se,lbs) ->
                     ((let uu____3129 = log env  in
                       if uu____3129
                       then
                         let _0_629 =
                           let _0_628 =
                             FStar_All.pipe_right (Prims.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____3136 =
                                         let _0_625 =
                                           ((FStar_Util.right
                                               lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env _0_625
                                          in
                                       match uu____3136 with
                                       | None  -> true
                                       | uu____3148 -> false  in
                                     if should_log
                                     then
                                       let _0_627 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let _0_626 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         _0_627 _0_626
                                     else ""))
                              in
                           FStar_All.pipe_right _0_628
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" _0_629
                       else ());
                      (let env = FStar_TypeChecker_Env.push_sigelt env se  in
                       ([se], env, []))))))

let for_export :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list)
  =
  fun hidden  ->
    fun se  ->
      let is_abstract quals =
        FStar_All.pipe_right quals
          (FStar_Util.for_some
             (fun uu___80_3181  ->
                match uu___80_3181 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____3182 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____3190 -> false  in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____3195 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____3208,r) ->
          let uu____3216 = is_abstract quals  in
          if uu____3216
          then
            let for_export_bundle se uu____3235 =
              match uu____3235 with
              | (out,hidden) ->
                  (match se with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____3258,uu____3259,quals,r) ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (let _0_630 =
                              FStar_Syntax_Util.maybe_tot_arrow bs t  in
                            (l, us, _0_630, (FStar_Syntax_Syntax.Assumption
                              :: FStar_Syntax_Syntax.New :: quals), r))
                          in
                       ((dec :: out), hidden)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____3275,uu____3276,uu____3277,uu____3278,r)
                       ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, us, t, [FStar_Syntax_Syntax.Assumption], r)
                          in
                       ((dec :: out), (l :: hidden))
                   | uu____3288 -> (out, hidden))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume
          (uu____3300,uu____3301,quals,uu____3303) ->
          let uu____3306 = is_abstract quals  in
          if uu____3306 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____3323 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____3323
          then
            ([FStar_Syntax_Syntax.Sig_declare_typ
                (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
              hidden))
          else
            (let uu____3333 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___81_3335  ->
                       match uu___81_3335 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____3338 -> false))
                in
             if uu____3333 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____3348 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____3360,uu____3361,quals,uu____3363) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____3381 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____3381
          then ([], hidden)
          else
            (let dec =
               FStar_Syntax_Syntax.Sig_declare_typ
                 (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                   (lb.FStar_Syntax_Syntax.lbunivs),
                   (lb.FStar_Syntax_Syntax.lbtyp),
                   [FStar_Syntax_Syntax.Assumption],
                   (FStar_Ident.range_of_lid lid))
                in
             ([dec], (lid :: hidden)))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____3405) ->
          let uu____3412 = is_abstract quals  in
          if uu____3412
          then
            let _0_632 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      FStar_Syntax_Syntax.Sig_declare_typ
                        (let _0_631 =
                           ((FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         (_0_631, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp),
                           (FStar_Syntax_Syntax.Assumption :: quals), r))))
               in
            (_0_632, hidden)
          else ([se], hidden)
  
let tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____3469 se =
        match uu____3469 with
        | (ses,exports,env,hidden) ->
            ((let uu____3499 =
                FStar_TypeChecker_Env.debug env FStar_Options.Low  in
              if uu____3499
              then
                let _0_633 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" _0_633
              else ());
             (let uu____3501 = tc_decl env se  in
              match uu____3501 with
              | (ses',env,ses_elaborated) ->
                  ((let uu____3525 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "LogTypes"))
                       in
                    if uu____3525
                    then
                      let _0_636 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se  ->
                               let _0_635 =
                                 let _0_634 =
                                   FStar_Syntax_Print.sigelt_to_string se  in
                                 Prims.strcat _0_634 "\n"  in
                               Prims.strcat s _0_635) "" ses'
                         in
                      FStar_Util.print1 "Checked: %s\n" _0_636
                    else ());
                   FStar_List.iter
                     (fun se  ->
                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env se) ses';
                   (let uu____3531 =
                      let accum_exports_hidden uu____3549 se =
                        match uu____3549 with
                        | (exports,hidden) ->
                            let uu____3565 = for_export hidden se  in
                            (match uu____3565 with
                             | (se_exported,hidden) ->
                                 ((FStar_List.rev_append se_exported exports),
                                   hidden))
                         in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'
                       in
                    match uu____3531 with
                    | (exports,hidden) ->
                        (((FStar_List.rev_append ses' ses), exports, env,
                           hidden), ses_elaborated)))))
         in
      let uu____3615 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses  in
      match uu____3615 with
      | (ses,exports,env,uu____3641) ->
          ((FStar_List.rev_append ses []),
            (FStar_List.rev_append exports []), env)
  
let tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let action = if verify then "Verifying" else "Lax-checking"  in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation"  in
      (let uu____3666 = FStar_Options.debug_any ()  in
       if uu____3666
       then
         FStar_Util.print3 "%s %s of %s\n" action label
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
          in
       let msg = Prims.strcat "Internals for " name  in
       let env =
         let uu___100_3672 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___100_3672.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___100_3672.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___100_3672.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___100_3672.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___100_3672.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___100_3672.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___100_3672.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___100_3672.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___100_3672.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___100_3672.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___100_3672.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___100_3672.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___100_3672.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___100_3672.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___100_3672.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___100_3672.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___100_3672.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___100_3672.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___100_3672.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___100_3672.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___100_3672.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___100_3672.FStar_TypeChecker_Env.qname_and_index)
         }  in
       (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env =
          FStar_TypeChecker_Env.set_current_module env
            modul.FStar_Syntax_Syntax.name
           in
        let uu____3675 = tc_decls env modul.FStar_Syntax_Syntax.declarations
           in
        match uu____3675 with
        | (ses,exports,env) ->
            ((let uu___101_3693 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___101_3693.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___101_3693.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___101_3693.FStar_Syntax_Syntax.is_interface)
              }), exports, env)))
  
let tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____3709 = tc_decls env decls  in
        match uu____3709 with
        | (ses,exports,env) ->
            let modul =
              let uu___102_3727 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___102_3727.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___102_3727.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___102_3727.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul, exports, env)
  
let check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env =
          let uu___103_3741 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___103_3741.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___103_3741.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___103_3741.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___103_3741.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___103_3741.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___103_3741.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___103_3741.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___103_3741.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___103_3741.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___103_3741.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___103_3741.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___103_3741.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___103_3741.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___103_3741.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___103_3741.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___103_3741.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___103_3741.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___103_3741.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___103_3741.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___103_3741.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___103_3741.FStar_TypeChecker_Env.qname_and_index)
          }  in
        let check_term lid univs t =
          let uu____3752 = FStar_Syntax_Subst.open_univ_vars univs t  in
          match uu____3752 with
          | (univs,t) ->
              ((let uu____3758 =
                  let _0_637 =
                    FStar_TypeChecker_Env.debug
                      (FStar_TypeChecker_Env.set_current_module env
                         modul.FStar_Syntax_Syntax.name)
                     in
                  FStar_All.pipe_left _0_637 (FStar_Options.Other "Exports")
                   in
                if uu____3758
                then
                  let _0_641 = FStar_Syntax_Print.lid_to_string lid  in
                  let _0_640 =
                    let _0_638 =
                      FStar_All.pipe_right univs
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right _0_638 (FStar_String.concat ", ")
                     in
                  let _0_639 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    _0_641 _0_640 _0_639
                else ());
               (let env = FStar_TypeChecker_Env.push_univ_vars env univs  in
                let _0_642 = FStar_TypeChecker_TcTerm.tc_trivial_guard env t
                   in
                FStar_All.pipe_right _0_642 Prims.ignore))
           in
        let check_term lid univs t =
          FStar_Errors.message_prefix.FStar_Errors.set_prefix
            (let _0_644 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let _0_643 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               _0_644 _0_643);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt uu___82_3783 =
          match uu___82_3783 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____3786,uu____3787)
              ->
              let uu____3794 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private))
                 in
              if uu____3794
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs,binders,typ,uu____3802,uu____3803,uu____3804,r) ->
              let t =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow
                      (let _0_645 = FStar_Syntax_Syntax.mk_Total typ  in
                       (binders, _0_645)))) None r
                 in
              check_term l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs,t,uu____3826,uu____3827,uu____3828,uu____3829,uu____3830)
              -> check_term l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs,t,quals,uu____3839)
              ->
              let uu____3842 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private))
                 in
              if uu____3842 then check_term l univs t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____3845,lbs),uu____3847,uu____3848,quals,uu____3850) ->
              let uu____3862 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private))
                 in
              if uu____3862
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        check_term
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs,binders,comp,quals,flags,r) ->
              let uu____3883 =
                Prims.op_Negation
                  (FStar_All.pipe_right quals
                     (FStar_List.contains FStar_Syntax_Syntax.Private))
                 in
              if uu____3883
              then
                let arrow =
                  (FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (binders, comp))) None r
                   in
                check_term l univs arrow
              else ()
          | FStar_Syntax_Syntax.Sig_main _
            |FStar_Syntax_Syntax.Sig_assume _
             |FStar_Syntax_Syntax.Sig_new_effect _
              |FStar_Syntax_Syntax.Sig_new_effect_for_free _
               |FStar_Syntax_Syntax.Sig_sub_effect _
                |FStar_Syntax_Syntax.Sig_pragma _
              -> ()
           in
        if
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then ()
        else FStar_List.iter check_sigelt exports
  
let finish_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelts ->
        (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let modul =
          let uu___104_3916 = modul  in
          {
            FStar_Syntax_Syntax.name =
              (uu___104_3916.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___104_3916.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          }  in
        let env = FStar_TypeChecker_Env.finish_module env modul  in
        (let uu____3919 = Prims.op_Negation (FStar_Options.lax ())  in
         if uu____3919 then check_exports env modul exports else ());
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env modul;
        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____3925 = Prims.op_Negation (FStar_Options.interactive ())
            in
         if uu____3925
         then
           let _0_646 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_right _0_646 Prims.ignore
         else ());
        (modul, env)
  
let tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____3935 = tc_partial_modul env modul  in
      match uu____3935 with
      | (modul,non_private_decls,env) ->
          finish_partial_modul env modul non_private_decls
  
let check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____3956 = FStar_Options.debug_any ()  in
       if uu____3956
       then
         let _0_647 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           _0_647
       else ());
      (let env =
         let uu___105_3960 = env  in
         let _0_648 =
           Prims.op_Negation
             (FStar_Options.should_verify
                (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
            in
         {
           FStar_TypeChecker_Env.solver =
             (uu___105_3960.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___105_3960.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___105_3960.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___105_3960.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___105_3960.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___105_3960.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___105_3960.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___105_3960.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___105_3960.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___105_3960.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___105_3960.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___105_3960.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___105_3960.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___105_3960.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___105_3960.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___105_3960.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___105_3960.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___105_3960.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = _0_648;
           FStar_TypeChecker_Env.lax_universes =
             (uu___105_3960.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___105_3960.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___105_3960.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___105_3960.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___105_3960.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____3961 = tc_modul env m  in
       match uu____3961 with
       | (m,env) ->
           ((let uu____3969 =
               FStar_Options.dump_module
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____3969
             then
               let _0_649 = FStar_Syntax_Print.modul_to_string m  in
               FStar_Util.print1 "%s\n" _0_649
             else ());
            (let uu____3972 =
               (FStar_Options.dump_module
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____3972
             then
               let normalize_toplevel_lets uu___83_3976 =
                 match uu___83_3976 with
                 | FStar_Syntax_Syntax.Sig_let ((b,lbs),r,ids,qs,attrs) ->
                     let n =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Reify;
                         FStar_TypeChecker_Normalize.Inlining;
                         FStar_TypeChecker_Normalize.Primops;
                         FStar_TypeChecker_Normalize.UnfoldUntil
                           FStar_Syntax_Syntax.Delta_constant;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                        in
                     let update lb =
                       let uu____4003 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____4003 with
                       | (univnames,e) ->
                           let uu___106_4008 = lb  in
                           let _0_651 =
                             let _0_650 =
                               FStar_TypeChecker_Env.push_univ_vars env
                                 univnames
                                in
                             n _0_650 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___106_4008.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___106_4008.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___106_4008.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___106_4008.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = _0_651
                           }
                        in
                     FStar_Syntax_Syntax.Sig_let
                       (let _0_653 =
                          let _0_652 = FStar_List.map update lbs  in
                          (b, _0_652)  in
                        (_0_653, r, ids, qs, attrs))
                 | se -> se  in
               let normalized_module =
                 let uu___107_4018 = m  in
                 let _0_654 =
                   FStar_List.map normalize_toplevel_lets
                     m.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___107_4018.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = _0_654;
                   FStar_Syntax_Syntax.exports =
                     (uu___107_4018.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___107_4018.FStar_Syntax_Syntax.is_interface)
                 }  in
               let _0_655 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" _0_655
             else ());
            (m, env)))
  
