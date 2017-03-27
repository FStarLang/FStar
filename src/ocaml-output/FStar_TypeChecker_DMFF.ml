open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const } 
let gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.EraseUniverses] env wp_a
               in
            let a =
              let uu___95_64 = a  in
              let _0_201 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___95_64.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___95_64.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = _0_201
              }  in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s  in
            (let uu____70 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____70
             then
               (d "Elaborating extra WP combinators";
                (let _0_202 = FStar_Syntax_Print.term_to_string wp_a  in
                 FStar_Util.print1 "wp_a is: %s\n" _0_202))
             else ());
            (let rec collect_binders t =
               let uu____80 =
                 (let _0_203 = FStar_Syntax_Subst.compress t  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_203).FStar_Syntax_Syntax.n
                  in
               match uu____80 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t,uu____102) -> t
                     | uu____109 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let _0_204 = collect_binders rest  in
                   FStar_List.append bs _0_204
               | FStar_Syntax_Syntax.Tm_type uu____114 -> []
               | uu____117 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name =
               FStar_Ident.lid_of_path
                 (FStar_Ident.path_of_text
                    (Prims.strcat
                       (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname)
                       (Prims.strcat "_" name))) FStar_Range.dummyRange
                in
             let gamma =
               let _0_205 = collect_binders wp_a  in
               FStar_All.pipe_right _0_205 FStar_Syntax_Util.name_binders  in
             (let uu____136 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____136
              then
                d
                  (let _0_206 =
                     FStar_Syntax_Print.binders_to_string ", " gamma  in
                   FStar_Util.format1 "Gamma is %s\n" _0_206)
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk x =
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange  in
              let sigelts = FStar_Util.mk_ref []  in
              let register env lident def =
                let uu____168 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env lident
                    def
                   in
                match uu____168 with
                | (sigelt,fv) ->
                    ((let _0_208 =
                        let _0_207 = FStar_ST.read sigelts  in sigelt ::
                          _0_207
                         in
                      FStar_ST.write sigelts _0_208);
                     fv)
                 in
              let binders_of_list =
                FStar_List.map
                  (fun uu____193  ->
                     match uu____193 with
                     | (t,b) ->
                         let _0_209 = FStar_Syntax_Syntax.as_implicit b  in
                         (t, _0_209))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let _0_210 = FStar_Syntax_Syntax.as_implicit true  in
                     ((Prims.fst t), _0_210))
                 in
              let args_of_binders =
                FStar_List.map
                  (fun bv  ->
                     FStar_Syntax_Syntax.as_arg
                       (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv)))
                 in
              let uu____228 =
                let uu____240 =
                  let mk f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype
                       in
                    let body =
                      let _0_211 = f (FStar_Syntax_Syntax.bv_to_name t)  in
                      FStar_Syntax_Util.arrow gamma _0_211  in
                    let _0_216 =
                      let _0_215 =
                        let _0_214 = FStar_Syntax_Syntax.mk_binder a  in
                        let _0_213 =
                          let _0_212 = FStar_Syntax_Syntax.mk_binder t  in
                          [_0_212]  in
                        _0_214 :: _0_213  in
                      FStar_List.append binders _0_215  in
                    FStar_Syntax_Util.abs _0_216 body None  in
                  let _0_218 = mk FStar_Syntax_Syntax.mk_Total  in
                  let _0_217 = mk FStar_Syntax_Syntax.mk_GTotal  in
                  (_0_218, _0_217)  in
                match uu____240 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app fv t =
                      mk
                        (FStar_Syntax_Syntax.Tm_app
                           (let _0_229 =
                              let _0_228 =
                                FStar_List.map
                                  (fun uu____302  ->
                                     match uu____302 with
                                     | (bv,uu____308) ->
                                         let _0_220 =
                                           FStar_Syntax_Syntax.bv_to_name bv
                                            in
                                         let _0_219 =
                                           FStar_Syntax_Syntax.as_implicit
                                             false
                                            in
                                         (_0_220, _0_219)) binders
                                 in
                              let _0_227 =
                                let _0_226 =
                                  let _0_222 =
                                    FStar_Syntax_Syntax.bv_to_name a  in
                                  let _0_221 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (_0_222, _0_221)  in
                                let _0_225 =
                                  let _0_224 =
                                    let _0_223 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (t, _0_223)  in
                                  [_0_224]  in
                                _0_226 :: _0_225  in
                              FStar_List.append _0_228 _0_227  in
                            (fv, _0_229)))
                       in
                    (env, (mk_app ctx_fv), (mk_app gctx_fv))
                 in
              match uu____228 with
              | (env,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype
                       in
                    let x =
                      let _0_230 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x" None _0_230  in
                    let ret =
                      Some
                        (FStar_Util.Inl
                           (let _0_231 =
                              FStar_Syntax_Syntax.mk_Total
                                (mk_ctx (FStar_Syntax_Syntax.bv_to_name t))
                               in
                            FStar_TypeChecker_Env.lcomp_of_comp env _0_231))
                       in
                    let body =
                      let _0_232 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma _0_232 ret  in
                    let _0_235 =
                      let _0_234 = mk_all_implicit binders  in
                      let _0_233 =
                        binders_of_list [(a, true); (t, true); (x, false)]
                         in
                      FStar_List.append _0_234 _0_233  in
                    FStar_Syntax_Util.abs _0_235 body ret  in
                  let c_pure =
                    let _0_236 = mk_lid "pure"  in register env _0_236 c_pure
                     in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let l =
                      let _0_241 =
                        mk_gctx
                          (let _0_240 =
                             let _0_238 =
                               FStar_Syntax_Syntax.mk_binder
                                 (let _0_237 =
                                    FStar_Syntax_Syntax.bv_to_name t1  in
                                  FStar_Syntax_Syntax.new_bv None _0_237)
                                in
                             [_0_238]  in
                           let _0_239 =
                             FStar_Syntax_Syntax.mk_GTotal
                               (FStar_Syntax_Syntax.bv_to_name t2)
                              in
                           FStar_Syntax_Util.arrow _0_240 _0_239)
                         in
                      FStar_Syntax_Syntax.gen_bv "l" None _0_241  in
                    let r =
                      let _0_242 =
                        mk_gctx (FStar_Syntax_Syntax.bv_to_name t1)  in
                      FStar_Syntax_Syntax.gen_bv "r" None _0_242  in
                    let ret =
                      Some
                        (FStar_Util.Inl
                           (let _0_243 =
                              FStar_Syntax_Syntax.mk_Total
                                (mk_gctx (FStar_Syntax_Syntax.bv_to_name t2))
                               in
                            FStar_TypeChecker_Env.lcomp_of_comp env _0_243))
                       in
                    let outer_body =
                      let gamma_as_args = args_of_binders gamma  in
                      let inner_body =
                        let _0_248 = FStar_Syntax_Syntax.bv_to_name l  in
                        let _0_247 =
                          let _0_246 =
                            let _0_245 =
                              FStar_Syntax_Syntax.as_arg
                                (let _0_244 =
                                   FStar_Syntax_Syntax.bv_to_name r  in
                                 FStar_Syntax_Util.mk_app _0_244
                                   gamma_as_args)
                               in
                            [_0_245]  in
                          FStar_List.append gamma_as_args _0_246  in
                        FStar_Syntax_Util.mk_app _0_248 _0_247  in
                      FStar_Syntax_Util.abs gamma inner_body ret  in
                    let _0_251 =
                      let _0_250 = mk_all_implicit binders  in
                      let _0_249 =
                        binders_of_list
                          [(a, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append _0_250 _0_249  in
                    FStar_Syntax_Util.abs _0_251 outer_body ret  in
                  let c_app =
                    let _0_252 = mk_lid "app"  in register env _0_252 c_app
                     in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let _0_255 =
                        let _0_253 =
                          FStar_Syntax_Syntax.null_binder
                            (FStar_Syntax_Syntax.bv_to_name t1)
                           in
                        [_0_253]  in
                      let _0_254 =
                        FStar_Syntax_Syntax.mk_GTotal
                          (FStar_Syntax_Syntax.bv_to_name t2)
                         in
                      FStar_Syntax_Util.arrow _0_255 _0_254  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a1 =
                      let _0_256 =
                        mk_gctx (FStar_Syntax_Syntax.bv_to_name t1)  in
                      FStar_Syntax_Syntax.gen_bv "a1" None _0_256  in
                    let ret =
                      Some
                        (FStar_Util.Inl
                           (let _0_257 =
                              FStar_Syntax_Syntax.mk_Total
                                (mk_gctx (FStar_Syntax_Syntax.bv_to_name t2))
                               in
                            FStar_TypeChecker_Env.lcomp_of_comp env _0_257))
                       in
                    let _0_269 =
                      let _0_259 = mk_all_implicit binders  in
                      let _0_258 =
                        binders_of_list
                          [(a, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a1, false)]
                         in
                      FStar_List.append _0_259 _0_258  in
                    let _0_268 =
                      let _0_267 =
                        let _0_266 =
                          let _0_265 =
                            let _0_262 =
                              let _0_261 =
                                let _0_260 = FStar_Syntax_Syntax.bv_to_name f
                                   in
                                [_0_260]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                _0_261
                               in
                            FStar_Syntax_Util.mk_app c_pure _0_262  in
                          let _0_264 =
                            let _0_263 = FStar_Syntax_Syntax.bv_to_name a1
                               in
                            [_0_263]  in
                          _0_265 :: _0_264  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg _0_266  in
                      FStar_Syntax_Util.mk_app c_app _0_267  in
                    FStar_Syntax_Util.abs _0_269 _0_268 ret  in
                  let c_lift1 =
                    let _0_270 = mk_lid "lift1"  in
                    register env _0_270 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let _0_275 =
                        let _0_273 =
                          FStar_Syntax_Syntax.null_binder
                            (FStar_Syntax_Syntax.bv_to_name t1)
                           in
                        let _0_272 =
                          let _0_271 =
                            FStar_Syntax_Syntax.null_binder
                              (FStar_Syntax_Syntax.bv_to_name t2)
                             in
                          [_0_271]  in
                        _0_273 :: _0_272  in
                      let _0_274 =
                        FStar_Syntax_Syntax.mk_GTotal
                          (FStar_Syntax_Syntax.bv_to_name t3)
                         in
                      FStar_Syntax_Util.arrow _0_275 _0_274  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a1 =
                      let _0_276 =
                        mk_gctx (FStar_Syntax_Syntax.bv_to_name t1)  in
                      FStar_Syntax_Syntax.gen_bv "a1" None _0_276  in
                    let a2 =
                      let _0_277 =
                        mk_gctx (FStar_Syntax_Syntax.bv_to_name t2)  in
                      FStar_Syntax_Syntax.gen_bv "a2" None _0_277  in
                    let ret =
                      Some
                        (FStar_Util.Inl
                           (let _0_278 =
                              FStar_Syntax_Syntax.mk_Total
                                (mk_gctx (FStar_Syntax_Syntax.bv_to_name t3))
                               in
                            FStar_TypeChecker_Env.lcomp_of_comp env _0_278))
                       in
                    let _0_295 =
                      let _0_280 = mk_all_implicit binders  in
                      let _0_279 =
                        binders_of_list
                          [(a, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a1, false);
                          (a2, false)]
                         in
                      FStar_List.append _0_280 _0_279  in
                    let _0_294 =
                      let _0_293 =
                        let _0_292 =
                          let _0_291 =
                            let _0_288 =
                              let _0_287 =
                                let _0_286 =
                                  let _0_283 =
                                    let _0_282 =
                                      let _0_281 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [_0_281]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      _0_282
                                     in
                                  FStar_Syntax_Util.mk_app c_pure _0_283  in
                                let _0_285 =
                                  let _0_284 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  [_0_284]  in
                                _0_286 :: _0_285  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                _0_287
                               in
                            FStar_Syntax_Util.mk_app c_app _0_288  in
                          let _0_290 =
                            let _0_289 = FStar_Syntax_Syntax.bv_to_name a2
                               in
                            [_0_289]  in
                          _0_291 :: _0_290  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg _0_292  in
                      FStar_Syntax_Util.mk_app c_app _0_293  in
                    FStar_Syntax_Util.abs _0_295 _0_294 ret  in
                  let c_lift2 =
                    let _0_296 = mk_lid "lift2"  in
                    register env _0_296 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let _0_299 =
                        let _0_297 =
                          FStar_Syntax_Syntax.null_binder
                            (FStar_Syntax_Syntax.bv_to_name t1)
                           in
                        [_0_297]  in
                      let _0_298 =
                        FStar_Syntax_Syntax.mk_Total
                          (mk_gctx (FStar_Syntax_Syntax.bv_to_name t2))
                         in
                      FStar_Syntax_Util.arrow _0_299 _0_298  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let ret =
                      Some
                        (FStar_Util.Inl
                           (let _0_303 =
                              FStar_Syntax_Syntax.mk_Total
                                (mk_ctx
                                   (let _0_302 =
                                      let _0_300 =
                                        FStar_Syntax_Syntax.null_binder
                                          (FStar_Syntax_Syntax.bv_to_name t1)
                                         in
                                      [_0_300]  in
                                    let _0_301 =
                                      FStar_Syntax_Syntax.mk_GTotal
                                        (FStar_Syntax_Syntax.bv_to_name t2)
                                       in
                                    FStar_Syntax_Util.arrow _0_302 _0_301))
                               in
                            FStar_TypeChecker_Env.lcomp_of_comp env _0_303))
                       in
                    let e1 =
                      let _0_304 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1" None _0_304  in
                    let body =
                      let _0_312 =
                        let _0_306 =
                          let _0_305 = FStar_Syntax_Syntax.mk_binder e1  in
                          [_0_305]  in
                        FStar_List.append gamma _0_306  in
                      let _0_311 =
                        let _0_310 = FStar_Syntax_Syntax.bv_to_name f  in
                        let _0_309 =
                          let _0_308 =
                            FStar_Syntax_Syntax.as_arg
                              (FStar_Syntax_Syntax.bv_to_name e1)
                             in
                          let _0_307 = args_of_binders gamma  in _0_308 ::
                            _0_307
                           in
                        FStar_Syntax_Util.mk_app _0_310 _0_309  in
                      FStar_Syntax_Util.abs _0_312 _0_311 ret  in
                    let _0_315 =
                      let _0_314 = mk_all_implicit binders  in
                      let _0_313 =
                        binders_of_list
                          [(a, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append _0_314 _0_313  in
                    FStar_Syntax_Util.abs _0_315 body ret  in
                  let c_push =
                    let _0_316 = mk_lid "push"  in register env _0_316 c_push
                     in
                  let ret_tot_wp_a =
                    Some
                      (FStar_Util.Inl
                         (let _0_317 = FStar_Syntax_Syntax.mk_Total wp_a  in
                          FStar_TypeChecker_Env.lcomp_of_comp env _0_317))
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      mk
                        (FStar_Syntax_Syntax.Tm_app
                           (let _0_318 = args_of_binders binders  in
                            (c, _0_318)))
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      FStar_Syntax_Syntax.mk_Total
                        (let _0_323 =
                           let _0_321 = FStar_Syntax_Syntax.null_binder wp_a
                              in
                           let _0_320 =
                             let _0_319 =
                               FStar_Syntax_Syntax.null_binder wp_a  in
                             [_0_319]  in
                           _0_321 :: _0_320  in
                         let _0_322 = FStar_Syntax_Syntax.mk_Total wp_a  in
                         FStar_Syntax_Util.arrow _0_323 _0_322)
                       in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype
                       in
                    let _0_333 =
                      let _0_324 = FStar_Syntax_Syntax.binders_of_list [a; c]
                         in
                      FStar_List.append binders _0_324  in
                    let _0_332 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None
                         in
                      let _0_330 =
                        let _0_329 =
                          let _0_328 =
                            let _0_327 =
                              let _0_326 =
                                let _0_325 =
                                  FStar_Syntax_Syntax.as_arg
                                    (FStar_Syntax_Syntax.bv_to_name c)
                                   in
                                [_0_325]  in
                              FStar_Syntax_Util.mk_app l_ite _0_326  in
                            [_0_327]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg _0_328
                           in
                        FStar_Syntax_Util.mk_app c_lift2 _0_329  in
                      FStar_Syntax_Util.ascribe _0_330
                        (FStar_Util.Inr result_comp)
                       in
                    let _0_331 =
                      Some
                        (FStar_Util.Inl
                           (FStar_TypeChecker_Env.lcomp_of_comp env
                              result_comp))
                       in
                    FStar_Syntax_Util.abs _0_333 _0_332 _0_331  in
                  let wp_if_then_else =
                    let _0_334 = mk_lid "wp_if_then_else"  in
                    register env _0_334 wp_if_then_else  in
                  let wp_if_then_else = mk_generic_app wp_if_then_else  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q" None
                        FStar_Syntax_Util.ktype
                       in
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a  in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1")) None
                       in
                    let body =
                      let _0_344 =
                        let _0_343 =
                          let _0_342 =
                            let _0_339 =
                              let _0_338 =
                                let _0_337 =
                                  let _0_336 =
                                    let _0_335 =
                                      FStar_Syntax_Syntax.as_arg
                                        (FStar_Syntax_Syntax.bv_to_name q)
                                       in
                                    [_0_335]  in
                                  FStar_Syntax_Util.mk_app l_and _0_336  in
                                [_0_337]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                _0_338
                               in
                            FStar_Syntax_Util.mk_app c_pure _0_339  in
                          let _0_341 =
                            let _0_340 = FStar_Syntax_Syntax.bv_to_name wp
                               in
                            [_0_340]  in
                          _0_342 :: _0_341  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg _0_343  in
                      FStar_Syntax_Util.mk_app c_app _0_344  in
                    let _0_346 =
                      let _0_345 =
                        FStar_Syntax_Syntax.binders_of_list [a; q; wp]  in
                      FStar_List.append binders _0_345  in
                    FStar_Syntax_Util.abs _0_346 body ret_tot_wp_a  in
                  let wp_assert =
                    let _0_347 = mk_lid "wp_assert"  in
                    register env _0_347 wp_assert  in
                  let wp_assert = mk_generic_app wp_assert  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q" None
                        FStar_Syntax_Util.ktype
                       in
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a  in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1")) None
                       in
                    let body =
                      let _0_357 =
                        let _0_356 =
                          let _0_355 =
                            let _0_352 =
                              let _0_351 =
                                let _0_350 =
                                  let _0_349 =
                                    let _0_348 =
                                      FStar_Syntax_Syntax.as_arg
                                        (FStar_Syntax_Syntax.bv_to_name q)
                                       in
                                    [_0_348]  in
                                  FStar_Syntax_Util.mk_app l_imp _0_349  in
                                [_0_350]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                _0_351
                               in
                            FStar_Syntax_Util.mk_app c_pure _0_352  in
                          let _0_354 =
                            let _0_353 = FStar_Syntax_Syntax.bv_to_name wp
                               in
                            [_0_353]  in
                          _0_355 :: _0_354  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg _0_356  in
                      FStar_Syntax_Util.mk_app c_app _0_357  in
                    let _0_359 =
                      let _0_358 =
                        FStar_Syntax_Syntax.binders_of_list [a; q; wp]  in
                      FStar_List.append binders _0_358  in
                    FStar_Syntax_Util.abs _0_359 body ret_tot_wp_a  in
                  let wp_assume =
                    let _0_360 = mk_lid "wp_assume"  in
                    register env _0_360 wp_assume  in
                  let wp_assume = mk_generic_app wp_assume  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let _0_363 =
                        let _0_361 =
                          FStar_Syntax_Syntax.null_binder
                            (FStar_Syntax_Syntax.bv_to_name b)
                           in
                        [_0_361]  in
                      let _0_362 = FStar_Syntax_Syntax.mk_Total wp_a  in
                      FStar_Syntax_Util.arrow _0_363 _0_362  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let body =
                      let _0_372 =
                        let _0_371 =
                          let _0_370 =
                            let _0_364 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure _0_364  in
                          let _0_369 =
                            let _0_368 =
                              let _0_367 =
                                let _0_366 =
                                  let _0_365 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [_0_365]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  _0_366
                                 in
                              FStar_Syntax_Util.mk_app c_push _0_367  in
                            [_0_368]  in
                          _0_370 :: _0_369  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg _0_371  in
                      FStar_Syntax_Util.mk_app c_app _0_372  in
                    let _0_374 =
                      let _0_373 =
                        FStar_Syntax_Syntax.binders_of_list [a; b; f]  in
                      FStar_List.append binders _0_373  in
                    FStar_Syntax_Util.abs _0_374 body ret_tot_wp_a  in
                  let wp_close =
                    let _0_375 = mk_lid "wp_close"  in
                    register env _0_375 wp_close  in
                  let wp_close = mk_generic_app wp_close  in
                  let ret_tot_type =
                    Some
                      (FStar_Util.Inl
                         (let _0_376 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype
                             in
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.lcomp_of_comp env) _0_376))
                     in
                  let ret_gtot_type =
                    Some
                      (FStar_Util.Inl
                         (let _0_377 =
                            FStar_Syntax_Syntax.mk_GTotal
                              FStar_Syntax_Util.ktype
                             in
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.lcomp_of_comp env) _0_377))
                     in
                  let mk_forall x body =
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_app
                          (let _0_381 =
                             let _0_380 =
                               FStar_Syntax_Syntax.as_arg
                                 (let _0_379 =
                                    let _0_378 =
                                      FStar_Syntax_Syntax.mk_binder x  in
                                    [_0_378]  in
                                  FStar_Syntax_Util.abs _0_379 body
                                    ret_tot_type)
                                in
                             [_0_380]  in
                           (FStar_Syntax_Util.tforall, _0_381)))) None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____703 =
                      (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                       in
                    match uu____703 with
                    | FStar_Syntax_Syntax.Tm_type uu____704 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____719  ->
                              match uu____719 with
                              | (b,uu____723) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          &&
                          (is_discrete
                             (FStar_TypeChecker_Env.result_typ env c))
                    | uu____724 -> true  in
                  let rec is_monotonic t =
                    let uu____729 =
                      (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                       in
                    match uu____729 with
                    | FStar_Syntax_Syntax.Tm_type uu____730 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____745  ->
                              match uu____745 with
                              | (b,uu____749) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          &&
                          (is_monotonic
                             (FStar_TypeChecker_Env.result_typ env c))
                    | uu____750 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel = mk_rel rel  in
                    let t =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env t
                       in
                    let uu____802 =
                      (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                       in
                    match uu____802 with
                    | FStar_Syntax_Syntax.Tm_type uu____803 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                      (binder::[],{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.GTotal (b,_);
                                    FStar_Syntax_Syntax.tk = _;
                                    FStar_Syntax_Syntax.pos = _;
                                    FStar_Syntax_Syntax.vars = _;_})
                      |FStar_Syntax_Syntax.Tm_arrow
                      (binder::[],{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Total (b,_);
                                    FStar_Syntax_Syntax.tk = _;
                                    FStar_Syntax_Syntax.pos = _;
                                    FStar_Syntax_Syntax.vars = _;_})
                        ->
                        let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____849 = (is_monotonic a) || (is_monotonic b)
                           in
                        if uu____849
                        then
                          let a1 = FStar_Syntax_Syntax.gen_bv "a1" None a  in
                          let body =
                            let _0_387 =
                              let _0_383 =
                                let _0_382 =
                                  FStar_Syntax_Syntax.as_arg
                                    (FStar_Syntax_Syntax.bv_to_name a1)
                                   in
                                [_0_382]  in
                              FStar_Syntax_Util.mk_app x _0_383  in
                            let _0_386 =
                              let _0_385 =
                                let _0_384 =
                                  FStar_Syntax_Syntax.as_arg
                                    (FStar_Syntax_Syntax.bv_to_name a1)
                                   in
                                [_0_384]  in
                              FStar_Syntax_Util.mk_app y _0_385  in
                            mk_rel b _0_387 _0_386  in
                          mk_forall a1 body
                        else
                          (let a1 = FStar_Syntax_Syntax.gen_bv "a1" None a
                              in
                           let a2 = FStar_Syntax_Syntax.gen_bv "a2" None a
                              in
                           let body =
                             let _0_397 =
                               let _0_389 = FStar_Syntax_Syntax.bv_to_name a1
                                  in
                               let _0_388 = FStar_Syntax_Syntax.bv_to_name a2
                                  in
                               mk_rel a _0_389 _0_388  in
                             let _0_396 =
                               let _0_395 =
                                 let _0_391 =
                                   let _0_390 =
                                     FStar_Syntax_Syntax.as_arg
                                       (FStar_Syntax_Syntax.bv_to_name a1)
                                      in
                                   [_0_390]  in
                                 FStar_Syntax_Util.mk_app x _0_391  in
                               let _0_394 =
                                 let _0_393 =
                                   let _0_392 =
                                     FStar_Syntax_Syntax.as_arg
                                       (FStar_Syntax_Syntax.bv_to_name a2)
                                      in
                                   [_0_392]  in
                                 FStar_Syntax_Util.mk_app y _0_393  in
                               mk_rel b _0_395 _0_394  in
                             FStar_Syntax_Util.mk_imp _0_397 _0_396  in
                           let _0_398 = mk_forall a2 body  in
                           mk_forall a1 _0_398)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders,comp) ->
                        let t =
                          let uu___96_876 = t  in
                          let _0_400 =
                            FStar_Syntax_Syntax.Tm_arrow
                              (let _0_399 =
                                 FStar_Syntax_Syntax.mk_Total
                                   (FStar_Syntax_Util.arrow binders comp)
                                  in
                               ([binder], _0_399))
                             in
                          {
                            FStar_Syntax_Syntax.n = _0_400;
                            FStar_Syntax_Syntax.tk =
                              (uu___96_876.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___96_876.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___96_876.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel t x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____888 ->
                        failwith "unhandled arrow"
                    | uu____896 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 = FStar_Syntax_Syntax.gen_bv "wp1" None wp_a  in
                    let wp2 = FStar_Syntax_Syntax.gen_bv "wp2" None wp_a  in
                    let rec mk_stronger t x y =
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] env t
                         in
                      let uu____911 =
                        (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                         in
                      match uu____911 with
                      | FStar_Syntax_Syntax.Tm_type uu____912 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head,args) when
                          FStar_Syntax_Util.is_tuple_constructor
                            (FStar_Syntax_Subst.compress head)
                          ->
                          let project i tuple =
                            let projector =
                              let _0_402 =
                                let _0_401 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env
                                  _0_401 i
                                 in
                              FStar_Syntax_Syntax.fvar _0_402
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)]
                             in
                          let uu____963 =
                            let uu____967 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____972  ->
                                     match uu____972 with
                                     | (t,q) ->
                                         let _0_404 = project i x  in
                                         let _0_403 = project i y  in
                                         mk_stronger t _0_404 _0_403) args
                               in
                            match uu____967 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____963 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                        (binders,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.GTotal (b,_);
                                   FStar_Syntax_Syntax.tk = _;
                                   FStar_Syntax_Syntax.pos = _;
                                   FStar_Syntax_Syntax.vars = _;_})
                        |FStar_Syntax_Syntax.Tm_arrow
                        (binders,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Total (b,_);
                                   FStar_Syntax_Syntax.tk = _;
                                   FStar_Syntax_Syntax.pos = _;
                                   FStar_Syntax_Syntax.vars = _;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1032  ->
                                   match uu____1032 with
                                   | (bv,q) ->
                                       let _0_406 =
                                         let _0_405 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" _0_405  in
                                       FStar_Syntax_Syntax.gen_bv _0_406 None
                                         bv.FStar_Syntax_Syntax.sort) binders
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 FStar_Syntax_Syntax.as_arg
                                   (FStar_Syntax_Syntax.bv_to_name ai)) bvs
                             in
                          let body =
                            let _0_408 = FStar_Syntax_Util.mk_app x args  in
                            let _0_407 = FStar_Syntax_Util.mk_app y args  in
                            mk_stronger b _0_408 _0_407  in
                          FStar_List.fold_right
                            (fun bv  -> fun body  -> mk_forall bv body) bvs
                            body
                      | uu____1043 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let _0_411 = FStar_Syntax_Util.unascribe wp_a  in
                      let _0_410 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let _0_409 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger _0_411 _0_410 _0_409  in
                    let _0_413 =
                      let _0_412 =
                        binders_of_list
                          [(a, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders _0_412  in
                    FStar_Syntax_Util.abs _0_413 body ret_tot_type  in
                  let stronger =
                    let _0_414 = mk_lid "stronger"  in
                    register env _0_414 stronger  in
                  let stronger = mk_generic_app stronger  in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a  in
                    let uu____1061 = FStar_Util.prefix gamma  in
                    match uu____1061 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (Prims.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq =
                            let _0_415 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm _0_415
                             in
                          let uu____1087 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq  in
                          match uu____1087 with
                          | Some (FStar_Syntax_Util.QAll (binders,[],body))
                              ->
                              let k_app =
                                let _0_416 = args_of_binders binders  in
                                FStar_Syntax_Util.mk_app k_tm _0_416  in
                              let guard_free =
                                FStar_Syntax_Syntax.fv_to_tm
                                  (FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.guard_free
                                     FStar_Syntax_Syntax.Delta_constant None)
                                 in
                              let pat =
                                let _0_418 =
                                  let _0_417 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [_0_417]  in
                                FStar_Syntax_Util.mk_app guard_free _0_418
                                 in
                              let pattern_guarded_body =
                                mk
                                  (FStar_Syntax_Syntax.Tm_meta
                                     (let _0_421 =
                                        FStar_Syntax_Syntax.Meta_pattern
                                          (let _0_420 =
                                             let _0_419 =
                                               FStar_Syntax_Syntax.as_arg pat
                                                in
                                             [_0_419]  in
                                           [_0_420])
                                         in
                                      (body, _0_421)))
                                 in
                              FStar_Syntax_Util.close_forall binders
                                pattern_guarded_body
                          | uu____1104 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let _0_429 =
                            let _0_428 =
                              let _0_427 =
                                let _0_426 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let _0_425 =
                                  let _0_424 = args_of_binders wp_args  in
                                  let _0_423 =
                                    let _0_422 =
                                      FStar_Syntax_Syntax.as_arg
                                        (FStar_Syntax_Syntax.bv_to_name k)
                                       in
                                    [_0_422]  in
                                  FStar_List.append _0_424 _0_423  in
                                FStar_Syntax_Util.mk_app _0_426 _0_425  in
                              FStar_Syntax_Util.mk_imp equiv _0_427  in
                            FStar_Syntax_Util.mk_forall k _0_428  in
                          FStar_Syntax_Util.abs gamma _0_429 ret_gtot_type
                           in
                        let _0_431 =
                          let _0_430 =
                            FStar_Syntax_Syntax.binders_of_list [a; wp]  in
                          FStar_List.append binders _0_430  in
                        FStar_Syntax_Util.abs _0_431 body ret_gtot_type
                     in
                  let wp_ite =
                    let _0_432 = mk_lid "wp_ite"  in
                    register env _0_432 wp_ite  in
                  let wp_ite = mk_generic_app wp_ite  in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a  in
                    let uu____1115 = FStar_Util.prefix gamma  in
                    match uu____1115 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let _0_436 =
                            let _0_435 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (Prims.fst post)
                               in
                            let _0_434 =
                              let _0_433 =
                                FStar_Syntax_Syntax.as_arg
                                  (FStar_Syntax_Syntax.bv_to_name x)
                                 in
                              [_0_433]  in
                            FStar_Syntax_Util.mk_app _0_435 _0_434  in
                          FStar_Syntax_Util.mk_forall x _0_436  in
                        let _0_439 =
                          let _0_438 =
                            let _0_437 =
                              FStar_Syntax_Syntax.binders_of_list [a]  in
                            FStar_List.append _0_437 gamma  in
                          FStar_List.append binders _0_438  in
                        FStar_Syntax_Util.abs _0_439 body ret_gtot_type
                     in
                  let null_wp =
                    let _0_440 = mk_lid "null_wp"  in
                    register env _0_440 null_wp  in
                  let null_wp = mk_generic_app null_wp  in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a  in
                    let body =
                      let _0_449 =
                        let _0_448 =
                          let _0_447 = FStar_Syntax_Syntax.bv_to_name a  in
                          let _0_446 =
                            let _0_445 =
                              let _0_442 =
                                let _0_441 =
                                  FStar_Syntax_Syntax.as_arg
                                    (FStar_Syntax_Syntax.bv_to_name a)
                                   in
                                [_0_441]  in
                              FStar_Syntax_Util.mk_app null_wp _0_442  in
                            let _0_444 =
                              let _0_443 = FStar_Syntax_Syntax.bv_to_name wp
                                 in
                              [_0_443]  in
                            _0_445 :: _0_444  in
                          _0_447 :: _0_446  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg _0_448  in
                      FStar_Syntax_Util.mk_app stronger _0_449  in
                    let _0_451 =
                      let _0_450 =
                        FStar_Syntax_Syntax.binders_of_list [a; wp]  in
                      FStar_List.append binders _0_450  in
                    FStar_Syntax_Util.abs _0_451 body ret_tot_type  in
                  let wp_trivial =
                    let _0_452 = mk_lid "wp_trivial"  in
                    register env _0_452 wp_trivial  in
                  let wp_trivial = mk_generic_app wp_trivial  in
                  ((let uu____1161 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "ED")
                       in
                    if uu____1161
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let _0_470 = FStar_List.rev (FStar_ST.read sigelts)  in
                    let _0_469 =
                      let uu___97_1170 = ed  in
                      let _0_468 =
                        let _0_453 = c wp_if_then_else  in ([], _0_453)  in
                      let _0_467 = let _0_454 = c wp_ite  in ([], _0_454)  in
                      let _0_466 = let _0_455 = c stronger  in ([], _0_455)
                         in
                      let _0_465 = let _0_456 = c wp_close  in ([], _0_456)
                         in
                      let _0_464 = let _0_457 = c wp_assert  in ([], _0_457)
                         in
                      let _0_463 = let _0_458 = c wp_assume  in ([], _0_458)
                         in
                      let _0_462 = let _0_459 = c null_wp  in ([], _0_459)
                         in
                      let _0_461 = let _0_460 = c wp_trivial  in ([], _0_460)
                         in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___97_1170.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___97_1170.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___97_1170.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___97_1170.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___97_1170.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___97_1170.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___97_1170.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___97_1170.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = _0_468;
                        FStar_Syntax_Syntax.ite_wp = _0_467;
                        FStar_Syntax_Syntax.stronger = _0_466;
                        FStar_Syntax_Syntax.close_wp = _0_465;
                        FStar_Syntax_Syntax.assert_p = _0_464;
                        FStar_Syntax_Syntax.assume_p = _0_463;
                        FStar_Syntax_Syntax.null_wp = _0_462;
                        FStar_Syntax_Syntax.trivial = _0_461;
                        FStar_Syntax_Syntax.repr =
                          (uu___97_1170.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___97_1170.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___97_1170.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___97_1170.FStar_Syntax_Syntax.actions)
                      }  in
                    (_0_470, _0_469)))))
  
type env_ = env
let get_env : env -> FStar_TypeChecker_Env.env = fun env  -> env.env 
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let uu___is_N : nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____1192 -> false 
let __proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0 
let uu___is_M : nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____1204 -> false 
let __proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let nm_of_comp : FStar_Syntax_Syntax.comp' -> nm =
  fun uu___84_1214  ->
    match uu___84_1214 with
    | FStar_Syntax_Syntax.Total (t,uu____1216) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___83_1225  ->
                match uu___83_1225 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____1226 -> false))
        -> M (Prims.fst (FStar_List.hd c.FStar_Syntax_Syntax.effect_args))
    | FStar_Syntax_Syntax.Comp c ->
        failwith
          (let _0_472 =
             let _0_471 = FStar_Syntax_Syntax.mk_Comp c  in
             FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _0_471  in
           FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _0_472)
    | FStar_Syntax_Syntax.GTotal uu____1234 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let string_of_nm : nm -> Prims.string =
  fun uu___85_1242  ->
    match uu___85_1242 with
    | N t ->
        let _0_473 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" _0_473
    | M t ->
        let _0_474 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" _0_474
  
let is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm =
  fun n  ->
    match n with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____1248,{ FStar_Syntax_Syntax.n = n;
                      FStar_Syntax_Syntax.tk = uu____1250;
                      FStar_Syntax_Syntax.pos = uu____1251;
                      FStar_Syntax_Syntax.vars = uu____1252;_})
        -> nm_of_comp n
    | uu____1263 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let is_monadic_comp c =
  let uu____1275 = nm_of_comp c.FStar_Syntax_Syntax.n  in
  match uu____1275 with | M uu____1276 -> true | N uu____1277 -> false 
exception Not_found 
let uu___is_Not_found : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____1281 -> false
  
let double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ0  ->
    let star_once typ0 =
      let _0_478 =
        let _0_476 =
          let _0_475 = FStar_Syntax_Syntax.new_bv None typ0  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_475  in
        [_0_476]  in
      let _0_477 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
      FStar_Syntax_Util.arrow _0_478 _0_477  in
    let _0_479 = FStar_All.pipe_right typ0 star_once  in
    FStar_All.pipe_left star_once _0_479
  
let rec mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax)
    ->
    env ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun mk  ->
    fun env  ->
      fun a  ->
        mk
          (FStar_Syntax_Syntax.Tm_arrow
             (let _0_484 =
                let _0_482 =
                  let _0_481 = FStar_Syntax_Syntax.null_bv (star_type' env a)
                     in
                  let _0_480 = FStar_Syntax_Syntax.as_implicit false  in
                  (_0_481, _0_480)  in
                [_0_482]  in
              let _0_483 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
              (_0_484, _0_483)))

and star_type' :
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk x = (FStar_Syntax_Syntax.mk x) None t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type = mk_star_to_type mk  in
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____1355) ->
          let binders =
            FStar_List.map
              (fun uu____1374  ->
                 match uu____1374 with
                 | (bv,aqual) ->
                     let _0_486 =
                       let uu___98_1381 = bv  in
                       let _0_485 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___98_1381.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___98_1381.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = _0_485
                       }  in
                     (_0_486, aqual)) binders
             in
          (match t.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____1382,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____1384);
                             FStar_Syntax_Syntax.tk = uu____1385;
                             FStar_Syntax_Syntax.pos = uu____1386;
                             FStar_Syntax_Syntax.vars = uu____1387;_})
               ->
               mk
                 (FStar_Syntax_Syntax.Tm_arrow
                    (let _0_487 =
                       FStar_Syntax_Syntax.mk_GTotal (star_type' env hn)  in
                     (binders, _0_487)))
           | uu____1407 ->
               let uu____1408 = is_monadic_arrow t.FStar_Syntax_Syntax.n  in
               (match uu____1408 with
                | N hn ->
                    mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         (let _0_488 =
                            FStar_Syntax_Syntax.mk_Total (star_type' env hn)
                             in
                          (binders, _0_488)))
                | M a ->
                    mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         (let _0_494 =
                            let _0_492 =
                              let _0_491 =
                                let _0_490 =
                                  FStar_Syntax_Syntax.null_bv
                                    (mk_star_to_type env a)
                                   in
                                let _0_489 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (_0_490, _0_489)  in
                              [_0_491]  in
                            FStar_List.append binders _0_492  in
                          let _0_493 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          (_0_494, _0_493)))))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let debug t s =
            let string_of_set f s =
              let elts = FStar_Util.set_elements s  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let _0_495 = f x  in
                    FStar_Util.string_builder_append strb _0_495);
                   FStar_List.iter
                     (fun x  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let _0_496 = f x  in
                         FStar_Util.string_builder_append strb _0_496)) xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let _0_498 = FStar_Syntax_Print.term_to_string t  in
            let _0_497 = string_of_set FStar_Syntax_Print.bv_to_string s  in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              _0_498 _0_497
             in
          let rec is_non_dependent_arrow ty n =
            let uu____1481 =
              (FStar_Syntax_Subst.compress ty).FStar_Syntax_Syntax.n  in
            match uu____1481 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____1494 =
                  Prims.op_Negation (FStar_Syntax_Util.is_tot_or_gtot_comp c)
                   in
                if uu____1494
                then false
                else
                  (try
                     let non_dependent_or_raise s ty =
                       let sinter =
                         let _0_499 = FStar_Syntax_Free.names ty  in
                         FStar_Util.set_intersect _0_499 s  in
                       let uu____1508 =
                         Prims.op_Negation (FStar_Util.set_is_empty sinter)
                          in
                       if uu____1508
                       then (debug ty sinter; Prims.raise Not_found)
                       else ()  in
                     let uu____1511 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____1511 with
                     | (binders,c) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____1522  ->
                                  match uu____1522 with
                                  | (bv,uu____1528) ->
                                      (non_dependent_or_raise s
                                         bv.FStar_Syntax_Syntax.sort;
                                       FStar_Util.set_add bv s))
                             FStar_Syntax_Syntax.no_names binders
                            in
                         let ct = FStar_TypeChecker_Env.result_typ env.env c
                            in
                         (non_dependent_or_raise s ct;
                          (let k = n - (FStar_List.length binders)  in
                           if k > (Prims.parse_int "0")
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found  -> false)
            | uu____1539 ->
                ((let _0_500 = FStar_Syntax_Print.term_to_string ty  in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    _0_500);
                 false)
             in
          let rec is_valid_application head =
            let uu____1545 =
              (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n  in
            match uu____1545 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid))
                  ||
                  (FStar_Syntax_Util.is_tuple_constructor
                     (FStar_Syntax_Subst.compress head))
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv when
                is_non_dependent_arrow
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty
                  (FStar_List.length args)
                ->
                let res =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Inlining;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env.env t
                   in
                (match res.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_app uu____1559 -> true
                 | uu____1569 ->
                     ((let _0_501 = FStar_Syntax_Print.term_to_string head
                          in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         _0_501);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
                true
            | FStar_Syntax_Syntax.Tm_uinst (t,uu____1574) ->
                is_valid_application t
            | uu____1579 -> false  in
          let uu____1580 = is_valid_application head  in
          if uu____1580
          then
            mk
              (FStar_Syntax_Syntax.Tm_app
                 (let _0_503 =
                    FStar_List.map
                      (fun uu____1592  ->
                         match uu____1592 with
                         | (t,qual) ->
                             let _0_502 = star_type' env t  in (_0_502, qual))
                      args
                     in
                  (head, _0_503)))
          else
            Prims.raise
              (FStar_Errors.Err
                 (let _0_504 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1
                    "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                    _0_504))
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_name _
         |FStar_Syntax_Syntax.Tm_type _|FStar_Syntax_Syntax.Tm_fvar _ -> t
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____1635 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____1635 with
           | (binders,repr) ->
               let env =
                 let uu___101_1641 = env  in
                 let _0_505 =
                   FStar_TypeChecker_Env.push_binders env.env binders  in
                 {
                   env = _0_505;
                   subst = (uu___101_1641.subst);
                   tc_const = (uu___101_1641.tc_const)
                 }  in
               let repr = star_type' env repr  in
               FStar_Syntax_Util.abs binders repr something)
      | FStar_Syntax_Syntax.Tm_refine (x,t) when false ->
          let x = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x.FStar_Syntax_Syntax.sort  in
          let subst = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x)]  in
          let t = FStar_Syntax_Subst.subst subst t  in
          let t = star_type' env t  in
          let subst = [FStar_Syntax_Syntax.NM (x, (Prims.parse_int "0"))]  in
          let t = FStar_Syntax_Subst.subst subst t  in
          mk
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___102_1658 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___102_1658.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___102_1658.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t))
      | FStar_Syntax_Syntax.Tm_meta (t,m) ->
          mk
            (FStar_Syntax_Syntax.Tm_meta
               (let _0_506 = star_type' env t  in (_0_506, m)))
      | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,something) ->
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (let _0_508 = star_type' env e  in
                let _0_507 = FStar_Util.Inl (star_type' env t)  in
                (_0_508, _0_507, something)))
      | FStar_Syntax_Syntax.Tm_ascribed uu____1693 ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_509 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_ascribed is outside of the definition language: %s"
                  _0_509))
      | FStar_Syntax_Syntax.Tm_refine uu____1706 ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_510 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_refine is outside of the definition language: %s"
                  _0_510))
      | FStar_Syntax_Syntax.Tm_uinst uu____1711 ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_511 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_uinst is outside of the definition language: %s" _0_511))
      | FStar_Syntax_Syntax.Tm_constant uu____1716 ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_512 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_constant is outside of the definition language: %s"
                  _0_512))
      | FStar_Syntax_Syntax.Tm_match uu____1717 ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_513 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_match is outside of the definition language: %s" _0_513))
      | FStar_Syntax_Syntax.Tm_let uu____1733 ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_514 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_let is outside of the definition language: %s" _0_514))
      | FStar_Syntax_Syntax.Tm_uvar uu____1741 ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_515 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_uvar is outside of the definition language: %s" _0_515))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          Prims.raise
            (FStar_Errors.Err
               (let _0_516 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.format1
                  "Tm_unknown is outside of the definition language: %s"
                  _0_516))
      | FStar_Syntax_Syntax.Tm_delayed uu____1750 -> failwith "impossible"

let is_monadic uu___87_1783 =
  match uu___87_1783 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
    { FStar_Syntax_Syntax.lcomp_name = _;
      FStar_Syntax_Syntax.lcomp_univs = _;
      FStar_Syntax_Syntax.lcomp_indices = _;
      FStar_Syntax_Syntax.lcomp_res_typ = _;
      FStar_Syntax_Syntax.lcomp_cflags = flags;
      FStar_Syntax_Syntax.lcomp_as_comp = _;_})|Some (FStar_Util.Inr
    (_,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___86_1822  ->
              match uu___86_1822 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____1823 -> false))
  
let rec is_C : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____1827 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
       in
    match uu____1827 with
    | FStar_Syntax_Syntax.Tm_app (head,args) when
        FStar_Syntax_Util.is_tuple_constructor head ->
        let r = is_C (Prims.fst (FStar_List.hd args))  in
        if r
        then
          ((let uu____1852 =
              Prims.op_Negation
                (FStar_List.for_all
                   (fun uu____1855  ->
                      match uu____1855 with | (h,uu____1859) -> is_C h) args)
               in
            if uu____1852 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____1863 =
              Prims.op_Negation
                (FStar_List.for_all
                   (fun uu____1866  ->
                      match uu____1866 with
                      | (h,uu____1870) -> Prims.op_Negation (is_C h)) args)
               in
            if uu____1863 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____1884 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____1884 with
         | M t ->
             ((let uu____1887 = is_C t  in
               if uu____1887 then failwith "not a C (C -> C)" else ());
              true)
         | N t -> is_C t)
    | FStar_Syntax_Syntax.Tm_meta (t,_)
      |FStar_Syntax_Syntax.Tm_uinst (t,_)|FStar_Syntax_Syntax.Tm_ascribed
       (t,_,_) -> is_C t
    | uu____1914 -> false
  
let mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk x = (FStar_Syntax_Syntax.mk x) None e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk env t  in
        let p = FStar_Syntax_Syntax.gen_bv "p'" None p_type  in
        let body =
          mk
            (FStar_Syntax_Syntax.Tm_app
               (let _0_520 = FStar_Syntax_Syntax.bv_to_name p  in
                let _0_519 =
                  let _0_518 =
                    let _0_517 = FStar_Syntax_Syntax.as_implicit false  in
                    (e, _0_517)  in
                  [_0_518]  in
                (_0_520, _0_519)))
           in
        let _0_522 =
          let _0_521 = FStar_Syntax_Syntax.mk_binder p  in [_0_521]  in
        FStar_Syntax_Util.abs _0_522 body None
  
let is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___88_1959  ->
    match uu___88_1959 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____1960 -> false
  
let rec check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos
           in
        let return_if uu____2102 =
          match uu____2102 with
          | (rec_nm,s_e,u_e) ->
              let check t1 t2 =
                let uu____2123 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (Prims.op_Negation
                       (FStar_TypeChecker_Rel.is_trivial
                          (FStar_TypeChecker_Rel.teq env.env t1 t2)))
                   in
                if uu____2123
                then
                  Prims.raise
                    (FStar_Errors.Err
                       (let _0_525 = FStar_Syntax_Print.term_to_string e  in
                        let _0_524 = FStar_Syntax_Print.term_to_string t1  in
                        let _0_523 = FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format3
                          "[check]: the expression [%s] has type [%s] but should have type [%s]"
                          _0_525 _0_524 _0_523))
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2)|(M t1,M t2) -> (check t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check t1 t2;
                    (let _0_526 = mk_return env t1 s_e  in
                     ((M t1), _0_526, u_e)))
               | (M t1,N t2) ->
                   Prims.raise
                     (FStar_Errors.Err
                        (let _0_529 = FStar_Syntax_Print.term_to_string e  in
                         let _0_528 = FStar_Syntax_Print.term_to_string t1
                            in
                         let _0_527 = FStar_Syntax_Print.term_to_string t2
                            in
                         FStar_Util.format3
                           "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                           _0_529 _0_528 _0_527)))
           in
        let ensure_m env e2 =
          let strip_m uu___89_2161 =
            match uu___89_2161 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____2171 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              Prims.raise
                (FStar_Errors.Error
                   (let _0_531 =
                      let _0_530 = FStar_Syntax_Print.term_to_string t  in
                      Prims.strcat
                        "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                        _0_530
                       in
                    (_0_531, (e2.FStar_Syntax_Syntax.pos))))
          | M uu____2185 -> strip_m (check env e2 context_nm)  in
        let uu____2186 =
          (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n  in
        match uu____2186 with
        | FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_name _
           |FStar_Syntax_Syntax.Tm_fvar _
            |FStar_Syntax_Syntax.Tm_abs _
             |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_app _
            -> return_if (infer env e)
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env  -> fun e2  -> check env e2 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env  -> fun body  -> check env body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e,_)
          |FStar_Syntax_Syntax.Tm_uinst (e,_)|FStar_Syntax_Syntax.Tm_ascribed
           (e,_,_) -> check env e context_nm
        | FStar_Syntax_Syntax.Tm_let uu____2262 ->
            failwith
              (let _0_532 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.format1 "[check]: Tm_let %s" _0_532)
        | FStar_Syntax_Syntax.Tm_type uu____2273 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____2277 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____2288 ->
            failwith
              (let _0_533 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.format1 "[check]: Tm_refine %s" _0_533)
        | FStar_Syntax_Syntax.Tm_uvar uu____2296 ->
            failwith
              (let _0_534 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.format1 "[check]: Tm_uvar %s" _0_534)
        | FStar_Syntax_Syntax.Tm_delayed uu____2308 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            failwith
              (let _0_535 = FStar_Syntax_Print.term_to_string e  in
               FStar_Util.format1 "[check]: Tm_unknown %s" _0_535)

and infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mk x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos  in
      let normalize =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env
         in
      let uu____2353 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
         in
      match uu____2353 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders = FStar_Syntax_Subst.open_binders binders  in
          let subst = FStar_Syntax_Subst.opening_of_binders binders  in
          let body = FStar_Syntax_Subst.subst subst body  in
          let env =
            let uu___103_2391 = env  in
            let _0_536 = FStar_TypeChecker_Env.push_binders env.env binders
               in
            {
              env = _0_536;
              subst = (uu___103_2391.subst);
              tc_const = (uu___103_2391.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____2400  ->
                 match uu____2400 with
                 | (bv,qual) ->
                     let sort = star_type' env bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___104_2408 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___104_2408.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___104_2408.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders
             in
          let uu____2409 =
            FStar_List.fold_left
              (fun uu____2418  ->
                 fun uu____2419  ->
                   match (uu____2418, uu____2419) with
                   | ((env,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____2447 = is_C c  in
                       if uu____2447
                       then
                         let xw =
                           let _0_537 = star_type' env c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "^w") None _0_537
                            in
                         let x =
                           let uu___105_2453 = bv  in
                           let _0_539 =
                             let _0_538 = FStar_Syntax_Syntax.bv_to_name xw
                                in
                             trans_F_ env c _0_538  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___105_2453.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___105_2453.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = _0_539
                           }  in
                         let env =
                           let uu___106_2455 = env  in
                           let _0_542 =
                             let _0_541 =
                               FStar_Syntax_Syntax.NT
                                 (let _0_540 =
                                    FStar_Syntax_Syntax.bv_to_name xw  in
                                  (bv, _0_540))
                                in
                             _0_541 :: (env.subst)  in
                           {
                             env = (uu___106_2455.env);
                             subst = _0_542;
                             tc_const = (uu___106_2455.tc_const)
                           }  in
                         let _0_546 =
                           let _0_545 = FStar_Syntax_Syntax.mk_binder x  in
                           let _0_544 =
                             let _0_543 = FStar_Syntax_Syntax.mk_binder xw
                                in
                             _0_543 :: acc  in
                           _0_545 :: _0_544  in
                         (env, _0_546)
                       else
                         (let x =
                            let uu___107_2459 = bv  in
                            let _0_547 =
                              star_type' env bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___107_2459.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___107_2459.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = _0_547
                            }  in
                          let _0_549 =
                            let _0_548 = FStar_Syntax_Syntax.mk_binder x  in
                            _0_548 :: acc  in
                          (env, _0_549))) (env, []) binders
             in
          (match uu____2409 with
           | (env,u_binders) ->
               let u_binders = FStar_List.rev u_binders  in
               let uu____2471 =
                 let check_what =
                   let uu____2483 = is_monadic what  in
                   if uu____2483 then check_m else check_n  in
                 let uu____2492 = check_what env body  in
                 match uu____2492 with
                 | (t,s_body,u_body) ->
                     let _0_550 =
                       comp_of_nm
                         (let uu____2502 = is_monadic what  in
                          if uu____2502 then M t else N t)
                        in
                     (_0_550, s_body, u_body)
                  in
               (match uu____2471 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders comp  in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____2543 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.lcomp_cflags
                              (FStar_Util.for_some
                                 (fun uu___90_2545  ->
                                    match uu___90_2545 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____2546 -> false))
                             in
                          if uu____2543
                          then
                            let double_starred_comp =
                              FStar_Syntax_Syntax.mk_Total
                                (let _0_552 =
                                   let _0_551 =
                                     lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                                      in
                                   FStar_TypeChecker_Env.result_typ env.env
                                     _0_551
                                    in
                                 FStar_All.pipe_left double_star _0_552)
                               in
                            let flags =
                              FStar_List.filter
                                (fun uu___91_2556  ->
                                   match uu___91_2556 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____2557 -> true)
                                lc.FStar_Syntax_Syntax.lcomp_cflags
                               in
                            Some
                              (FStar_Util.Inl
                                 (let _0_553 =
                                    FStar_Syntax_Util.comp_set_flags
                                      double_starred_comp flags
                                     in
                                  FStar_TypeChecker_Env.lcomp_of_comp 
                                    env.env _0_553))
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___108_2575 = lc  in
                                   {
                                     FStar_Syntax_Syntax.lcomp_name =
                                       (uu___108_2575.FStar_Syntax_Syntax.lcomp_name);
                                     FStar_Syntax_Syntax.lcomp_univs =
                                       (uu___108_2575.FStar_Syntax_Syntax.lcomp_univs);
                                     FStar_Syntax_Syntax.lcomp_indices =
                                       (uu___108_2575.FStar_Syntax_Syntax.lcomp_indices);
                                     FStar_Syntax_Syntax.lcomp_res_typ =
                                       (uu___108_2575.FStar_Syntax_Syntax.lcomp_res_typ);
                                     FStar_Syntax_Syntax.lcomp_cflags =
                                       (uu___108_2575.FStar_Syntax_Syntax.lcomp_cflags);
                                     FStar_Syntax_Syntax.lcomp_as_comp =
                                       (fun uu____2576  ->
                                          let c =
                                            lc.FStar_Syntax_Syntax.lcomp_as_comp
                                              ()
                                             in
                                          let nct =
                                            FStar_TypeChecker_Env.comp_as_normal_comp_typ
                                              env.env c
                                             in
                                          let result_typ =
                                            star_type' env
                                              (Prims.fst
                                                 nct.FStar_TypeChecker_Env.nct_result)
                                             in
                                          let nct' =
                                            let uu___109_2585 = nct  in
                                            let _0_554 =
                                              FStar_Syntax_Syntax.as_arg
                                                result_typ
                                               in
                                            {
                                              FStar_TypeChecker_Env.nct_name
                                                =
                                                (uu___109_2585.FStar_TypeChecker_Env.nct_name);
                                              FStar_TypeChecker_Env.nct_univs
                                                =
                                                (uu___109_2585.FStar_TypeChecker_Env.nct_univs);
                                              FStar_TypeChecker_Env.nct_indices
                                                =
                                                (uu___109_2585.FStar_TypeChecker_Env.nct_indices);
                                              FStar_TypeChecker_Env.nct_result
                                                = _0_554;
                                              FStar_TypeChecker_Env.nct_wp =
                                                (uu___109_2585.FStar_TypeChecker_Env.nct_wp);
                                              FStar_TypeChecker_Env.nct_flags
                                                =
                                                (uu___109_2585.FStar_TypeChecker_Env.nct_flags)
                                            }  in
                                          FStar_TypeChecker_Env.normal_comp_typ_as_comp
                                            env.env nct')
                                   })))
                      | Some (FStar_Util.Inr (lid,flags)) ->
                          Some
                            (FStar_Util.Inr
                               (let uu____2606 =
                                  FStar_All.pipe_right flags
                                    (FStar_Util.for_some
                                       (fun uu___92_2608  ->
                                          match uu___92_2608 with
                                          | FStar_Syntax_Syntax.CPS  -> true
                                          | uu____2609 -> false))
                                   in
                                if uu____2606
                                then
                                  let _0_555 =
                                    FStar_List.filter
                                      (fun uu___93_2614  ->
                                         match uu___93_2614 with
                                         | FStar_Syntax_Syntax.CPS  -> false
                                         | uu____2615 -> true) flags
                                     in
                                  (FStar_Syntax_Const.effect_Tot_lid, _0_555)
                                else (lid, flags)))
                       in
                    let uu____2618 =
                      let comp =
                        let _0_558 =
                          FStar_TypeChecker_Env.result_typ env.env comp  in
                        let _0_557 = is_monadic what  in
                        let _0_556 =
                          FStar_Syntax_Subst.subst env.subst s_body  in
                        trans_G env _0_558 _0_557 _0_556  in
                      let _0_560 =
                        FStar_Syntax_Util.ascribe u_body
                          (FStar_Util.Inr comp)
                         in
                      let _0_559 =
                        Some
                          (FStar_Util.Inl
                             (FStar_TypeChecker_Env.lcomp_of_comp env.env
                                comp))
                         in
                      (_0_560, _0_559)  in
                    (match uu____2618 with
                     | (u_body,u_what) ->
                         let s_body =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (s_binders, s_body, s_what))
                            in
                         let u_body =
                           FStar_Syntax_Subst.close u_binders u_body  in
                         let u_binders =
                           FStar_Syntax_Subst.close_binders u_binders  in
                         let u_term =
                           mk
                             (FStar_Syntax_Syntax.Tm_abs
                                (u_binders, u_body, u_what))
                            in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.ty = uu____2696;
                FStar_Syntax_Syntax.p = uu____2697;_};
            FStar_Syntax_Syntax.fv_delta = uu____2698;
            FStar_Syntax_Syntax.fv_qual = uu____2699;_}
          ->
          let uu____2705 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
          (match uu____2705 with
           | (uu____2711,t) ->
               let txt = FStar_Ident.text_of_lid lid  in
               let _0_561 = N (normalize t)  in (_0_561, e, e))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let uu____2730 = check_n env head  in
          (match uu____2730 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____2744 =
                   (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                 match uu____2744 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____2745 -> true
                 | uu____2753 -> false  in
               let rec flatten t =
                 let uu____2765 =
                   (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
                 match uu____2765 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t,uu____2775);
                                FStar_Syntax_Syntax.tk = uu____2776;
                                FStar_Syntax_Syntax.pos = uu____2777;
                                FStar_Syntax_Syntax.vars = uu____2778;_})
                     when is_arrow t ->
                     let uu____2795 = flatten t  in
                     (match uu____2795 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e,uu____2847,uu____2848)
                     -> flatten e
                 | uu____2867 ->
                     Prims.raise
                       (FStar_Errors.Err
                          (let _0_562 =
                             FStar_Syntax_Print.term_to_string t_head  in
                           FStar_Util.format1 "%s: not a function type"
                             _0_562))
                  in
               let uu____2875 = flatten t_head  in
               (match uu____2875 with
                | (binders,comp) ->
                    let n = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       Prims.raise
                         (FStar_Errors.Err
                            (let _0_565 = FStar_Util.string_of_int n  in
                             let _0_564 = FStar_Util.string_of_int (n' - n)
                                in
                             let _0_563 = FStar_Util.string_of_int n  in
                             FStar_Util.format3
                               "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                               _0_565 _0_564 _0_563))
                     else ();
                     (let uu____2932 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____2932 with
                      | (binders,comp) ->
                          let rec final_type subst uu____2959 args =
                            match uu____2959 with
                            | (binders,comp) ->
                                (match (binders, args) with
                                 | ([],[]) ->
                                     nm_of_comp
                                       (FStar_Syntax_Subst.subst_comp subst
                                          comp).FStar_Syntax_Syntax.n
                                 | (binders,[]) ->
                                     let uu____3018 =
                                       (FStar_Syntax_Subst.compress
                                          (let _0_566 =
                                             mk
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders, comp))
                                              in
                                           FStar_Syntax_Subst.subst subst
                                             _0_566)).FStar_Syntax_Syntax.n
                                        in
                                     (match uu____3018 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders,comp) ->
                                          N
                                            (mk
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (let _0_567 =
                                                     FStar_Syntax_Subst.close_comp
                                                       binders comp
                                                      in
                                                   (binders, _0_567))))
                                      | uu____3037 -> failwith "wat?")
                                 | ([],uu____3038::uu____3039) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____3064)::binders,(arg,uu____3067)::args)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst) (binders, comp) args)
                             in
                          let final_type = final_type [] (binders, comp) args
                             in
                          let uu____3101 = FStar_List.splitAt n' binders  in
                          (match uu____3101 with
                           | (binders,uu____3118) ->
                               let uu____3131 =
                                 FStar_List.split
                                   (FStar_List.map2
                                      (fun uu____3157  ->
                                         fun uu____3158  ->
                                           match (uu____3157, uu____3158)
                                           with
                                           | ((bv,uu____3175),(arg,q)) ->
                                               let uu____3182 =
                                                 (FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____3182 with
                                                | FStar_Syntax_Syntax.Tm_type
                                                    uu____3190 ->
                                                    let arg = (arg, q)  in
                                                    (arg, [arg])
                                                | uu____3203 ->
                                                    let uu____3204 =
                                                      check_n env arg  in
                                                    (match uu____3204 with
                                                     | (uu____3215,s_arg,u_arg)
                                                         ->
                                                         let _0_570 =
                                                           let uu____3223 =
                                                             is_C
                                                               bv.FStar_Syntax_Syntax.sort
                                                              in
                                                           if uu____3223
                                                           then
                                                             let _0_569 =
                                                               let _0_568 =
                                                                 FStar_Syntax_Subst.subst
                                                                   env.subst
                                                                   s_arg
                                                                  in
                                                               (_0_568, q)
                                                                in
                                                             [_0_569;
                                                             (u_arg, q)]
                                                           else [(u_arg, q)]
                                                            in
                                                         ((s_arg, q), _0_570))))
                                      binders args)
                                  in
                               (match uu____3131 with
                                | (s_args,u_args) ->
                                    let u_args = FStar_List.flatten u_args
                                       in
                                    let _0_572 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let _0_571 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args))
                                       in
                                    (final_type, _0_572, _0_571)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e,_)
        |FStar_Syntax_Syntax.Tm_meta (e,_)|FStar_Syntax_Syntax.Tm_ascribed
         (e,_,_) -> infer env e
      | FStar_Syntax_Syntax.Tm_constant c ->
          let _0_573 = N (env.tc_const c)  in (_0_573, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____3336 ->
          failwith
            (let _0_574 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.format1 "[infer]: Tm_let %s" _0_574)
      | FStar_Syntax_Syntax.Tm_type uu____3347 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____3351 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____3362 ->
          failwith
            (let _0_575 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.format1 "[infer]: Tm_refine %s" _0_575)
      | FStar_Syntax_Syntax.Tm_uvar uu____3370 ->
          failwith
            (let _0_576 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.format1 "[infer]: Tm_uvar %s" _0_576)
      | FStar_Syntax_Syntax.Tm_delayed uu____3382 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          failwith
            (let _0_577 = FStar_Syntax_Print.term_to_string e  in
             FStar_Util.format1 "[infer]: Tm_unknown %s" _0_577)

and mk_match :
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk x = FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos
             in
          let uu____3443 = check_n env e0  in
          match uu____3443 with
          | (uu____3450,s_e0,u_e0) ->
              let uu____3453 =
                FStar_List.split
                  (FStar_List.map
                     (fun b  ->
                        let uu____3500 = FStar_Syntax_Subst.open_branch b  in
                        match uu____3500 with
                        | (pat,None ,body) ->
                            let env =
                              let uu___110_3532 = env  in
                              let _0_579 =
                                let _0_578 = FStar_Syntax_Syntax.pat_bvs pat
                                   in
                                FStar_List.fold_left
                                  FStar_TypeChecker_Env.push_bv env.env
                                  _0_578
                                 in
                              {
                                env = _0_579;
                                subst = (uu___110_3532.subst);
                                tc_const = (uu___110_3532.tc_const)
                              }  in
                            let uu____3533 = f env body  in
                            (match uu____3533 with
                             | (nm,s_body,u_body) ->
                                 (nm, (pat, None, (s_body, u_body, body))))
                        | uu____3582 ->
                            Prims.raise
                              (FStar_Errors.Err
                                 "No when clauses in the definition language"))
                     branches)
                 in
              (match uu____3453 with
               | (nms,branches) ->
                   let t1 =
                     let uu____3634 = FStar_List.hd nms  in
                     match uu____3634 with | M t1|N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___94_3637  ->
                          match uu___94_3637 with
                          | M uu____3638 -> true
                          | uu____3639 -> false) nms
                      in
                   let uu____3640 =
                     FStar_List.unzip3
                       (FStar_List.map2
                          (fun nm  ->
                             fun uu____3710  ->
                               match uu____3710 with
                               | (pat,guard,(s_body,u_body,original_body)) ->
                                   (match (nm, has_m) with
                                    | (N t2,false )|(M t2,true ) ->
                                        (nm, (pat, guard, s_body),
                                          (pat, guard, u_body))
                                    | (N t2,true ) ->
                                        let uu____3806 =
                                          check env original_body (M t2)  in
                                        (match uu____3806 with
                                         | (uu____3829,s_body,u_body) ->
                                             ((M t2), (pat, guard, s_body),
                                               (pat, guard, u_body)))
                                    | (M uu____3858,false ) ->
                                        failwith "impossible")) nms branches)
                      in
                   (match uu____3640 with
                    | (nms,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_branches =
                            FStar_List.map
                              (fun uu____3961  ->
                                 match uu____3961 with
                                 | (pat,guard,s_body) ->
                                     let s_body =
                                       mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (let _0_583 =
                                               let _0_582 =
                                                 let _0_581 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     p
                                                    in
                                                 let _0_580 =
                                                   FStar_Syntax_Syntax.as_implicit
                                                     false
                                                    in
                                                 (_0_581, _0_580)  in
                                               [_0_582]  in
                                             (s_body, _0_583)))
                                        in
                                     (pat, guard, s_body)) s_branches
                             in
                          let s_branches =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches
                             in
                          let u_branches =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches
                             in
                          let s_e =
                            let _0_586 =
                              let _0_584 = FStar_Syntax_Syntax.mk_binder p
                                 in
                              [_0_584]  in
                            let _0_585 =
                              mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches))
                               in
                            FStar_Syntax_Util.abs _0_586 _0_585 None  in
                          let t1_star =
                            let _0_590 =
                              let _0_588 =
                                let _0_587 =
                                  FStar_Syntax_Syntax.new_bv None p_type  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder _0_587
                                 in
                              [_0_588]  in
                            let _0_589 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow _0_590 _0_589  in
                          let _0_592 =
                            mk
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, (FStar_Util.Inl t1_star), None))
                             in
                          let _0_591 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches))
                             in
                          ((M t1), _0_592, _0_591)
                        else
                          (let s_branches =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches
                              in
                           let u_branches =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches
                              in
                           let t1_star = t1  in
                           let _0_595 =
                             mk
                               (FStar_Syntax_Syntax.Tm_ascribed
                                  (let _0_593 =
                                     mk
                                       (FStar_Syntax_Syntax.Tm_match
                                          (s_e0, s_branches))
                                      in
                                   (_0_593, (FStar_Util.Inl t1_star), None)))
                              in
                           let _0_594 =
                             mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches))
                              in
                           ((N t1), _0_595, _0_594))))

and mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
                 FStar_Syntax_Syntax.term))
            -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk x =
              FStar_Syntax_Syntax.mk x None e2.FStar_Syntax_Syntax.pos  in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let _0_596 = FStar_Syntax_Syntax.mk_binder x  in [_0_596]  in
            let uu____4098 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____4098 with
            | (x_binders,e2) ->
                let uu____4106 = infer env e1  in
                (match uu____4106 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____4117 = is_C t1  in
                       if uu____4117
                       then
                         let uu___111_4118 = binding  in
                         let _0_598 =
                           let _0_597 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 _0_597  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___111_4118.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___111_4118.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = _0_598;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___111_4118.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___111_4118.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding  in
                     let env =
                       let uu___112_4121 = env  in
                       let _0_599 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___113_4122 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___113_4122.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___113_4122.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = _0_599;
                         subst = (uu___112_4121.subst);
                         tc_const = (uu___112_4121.tc_const)
                       }  in
                     let uu____4123 = proceed env e2  in
                     (match uu____4123 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___114_4134 = binding  in
                            let _0_600 =
                              star_type' env
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___114_4134.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___114_4134.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = _0_600;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___114_4134.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___114_4134.FStar_Syntax_Syntax.lbdef)
                            }  in
                          let _0_604 =
                            mk
                              (FStar_Syntax_Syntax.Tm_let
                                 (let _0_601 =
                                    FStar_Syntax_Subst.close x_binders s_e2
                                     in
                                  ((false,
                                     [(let uu___115_4143 = s_binding  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___115_4143.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___115_4143.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___115_4143.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___115_4143.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = s_e1
                                       })]), _0_601)))
                             in
                          let _0_603 =
                            mk
                              (FStar_Syntax_Syntax.Tm_let
                                 (let _0_602 =
                                    FStar_Syntax_Subst.close x_binders u_e2
                                     in
                                  ((false,
                                     [(let uu___116_4148 = u_binding  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___116_4148.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___116_4148.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___116_4148.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___116_4148.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = u_e1
                                       })]), _0_602)))
                             in
                          (nm_rec, _0_604, _0_603))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___117_4153 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___117_4153.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___117_4153.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___117_4153.FStar_Syntax_Syntax.lbdef)
                       }  in
                     let env =
                       let uu___118_4155 = env  in
                       let _0_605 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_4156 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_4156.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_4156.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = _0_605;
                         subst = (uu___118_4155.subst);
                         tc_const = (uu___118_4155.tc_const)
                       }  in
                     let uu____4157 = ensure_m env e2  in
                     (match uu____4157 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk env t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_e2 =
                            mk
                              (FStar_Syntax_Syntax.Tm_app
                                 (let _0_609 =
                                    let _0_608 =
                                      let _0_607 =
                                        FStar_Syntax_Syntax.bv_to_name p  in
                                      let _0_606 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (_0_607, _0_606)  in
                                    [_0_608]  in
                                  (s_e2, _0_609)))
                             in
                          let s_e2 =
                            FStar_Syntax_Util.abs x_binders s_e2 None  in
                          let body =
                            mk
                              (FStar_Syntax_Syntax.Tm_app
                                 (let _0_612 =
                                    let _0_611 =
                                      let _0_610 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (s_e2, _0_610)  in
                                    [_0_611]  in
                                  (s_e1, _0_612)))
                             in
                          let _0_617 =
                            let _0_614 =
                              let _0_613 = FStar_Syntax_Syntax.mk_binder p
                                 in
                              [_0_613]  in
                            FStar_Syntax_Util.abs _0_614 body None  in
                          let _0_616 =
                            mk
                              (FStar_Syntax_Syntax.Tm_let
                                 (let _0_615 =
                                    FStar_Syntax_Subst.close x_binders u_e2
                                     in
                                  ((false,
                                     [(let uu___120_4208 = u_binding  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___120_4208.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___120_4208.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___120_4208.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           (uu___120_4208.FStar_Syntax_Syntax.lbeff);
                                         FStar_Syntax_Syntax.lbdef = u_e1
                                       })]), _0_615)))
                             in
                          ((M t2), _0_617, _0_616)))

and check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        N
          (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
             e.FStar_Syntax_Syntax.pos)
         in
      let uu____4227 = check env e mn  in
      match uu____4227 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____4237 -> failwith "[check_n]: impossible"

and check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        M
          (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
             e.FStar_Syntax_Syntax.pos)
         in
      let uu____4262 = check env e mn  in
      match uu____4262 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____4272 -> failwith "[check_m]: impossible"

and comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      (let _0_619 = let _0_618 = FStar_Syntax_Syntax.as_arg t  in [_0_618]
          in
       {
         FStar_Syntax_Syntax.comp_typ_name = FStar_Syntax_Const.monadic_lid;
         FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
         FStar_Syntax_Syntax.effect_args = _0_619;
         FStar_Syntax_Syntax.flags =
           [FStar_Syntax_Syntax.CPS; FStar_Syntax_Syntax.TOTAL]
       })

and type_of_comp : env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ
  = fun env  -> fun t  -> FStar_TypeChecker_Env.result_typ env.env t

and trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____4289 = Prims.op_Negation (is_C c)  in
         if uu____4289 then failwith "not a C" else ());
        (let mk x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos
            in
         let uu____4301 =
           (FStar_Syntax_Subst.compress c).FStar_Syntax_Syntax.n  in
         match uu____4301 with
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             let uu____4318 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____4318 with
              | (wp_head,wp_args) ->
                  ((let uu____4345 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (Prims.op_Negation
                           (let _0_620 =
                              FStar_Syntax_Util.mk_tuple_data_lid
                                (FStar_List.length wp_args)
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.is_constructor wp_head _0_620))
                       in
                    if uu____4345 then failwith "mismatch" else ());
                   mk
                     (FStar_Syntax_Syntax.Tm_app
                        (let _0_624 =
                           FStar_List.map2
                             (fun uu____4377  ->
                                fun uu____4378  ->
                                  match (uu____4377, uu____4378) with
                                  | ((arg,q),(wp_arg,q')) ->
                                      let print_implicit q =
                                        let uu____4401 =
                                          FStar_Syntax_Syntax.is_implicit q
                                           in
                                        if uu____4401
                                        then "implicit"
                                        else "explicit"  in
                                      (if q <> q'
                                       then
                                         (let _0_622 = print_implicit q  in
                                          let _0_621 = print_implicit q'  in
                                          FStar_Util.print2_warning
                                            "Incoherent implicit qualifiers %b %b"
                                            _0_622 _0_621)
                                       else ();
                                       (let _0_623 = trans_F_ env arg wp_arg
                                           in
                                        (_0_623, q)))) args wp_args
                            in
                         (head, _0_624)))))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders = FStar_Syntax_Util.name_binders binders  in
             let uu____4421 = FStar_Syntax_Subst.open_comp binders comp  in
             (match uu____4421 with
              | (binders_orig,comp) ->
                  let uu____4426 =
                    FStar_List.split
                      (FStar_List.map
                         (fun uu____4444  ->
                            match uu____4444 with
                            | (bv,q) ->
                                let h = bv.FStar_Syntax_Syntax.sort  in
                                let uu____4457 = is_C h  in
                                if uu____4457
                                then
                                  let w' =
                                    let _0_625 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "-w'") None _0_625
                                     in
                                  let _0_630 =
                                    let _0_629 =
                                      let _0_628 =
                                        let _0_627 =
                                          FStar_Syntax_Syntax.null_bv
                                            (let _0_626 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 w'
                                                in
                                             trans_F_ env h _0_626)
                                           in
                                        (_0_627, q)  in
                                      [_0_628]  in
                                    (w', q) :: _0_629  in
                                  (w', _0_630)
                                else
                                  (let x =
                                     let _0_631 = star_type' env h  in
                                     FStar_Syntax_Syntax.gen_bv
                                       (Prims.strcat
                                          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                          "-x") None _0_631
                                      in
                                   (x, [(x, q)]))) binders_orig)
                     in
                  (match uu____4426 with
                   | (bvs,binders) ->
                       let binders = FStar_List.flatten binders  in
                       let comp =
                         let _0_633 =
                           let _0_632 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             _0_632
                            in
                         FStar_Syntax_Subst.subst_comp _0_633 comp  in
                       let app =
                         mk
                           (FStar_Syntax_Syntax.Tm_app
                              (let _0_636 =
                                 FStar_List.map
                                   (fun bv  ->
                                      let _0_635 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      let _0_634 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (_0_635, _0_634)) bvs
                                  in
                               (wp, _0_636)))
                          in
                       let comp =
                         let _0_638 = type_of_comp env comp  in
                         let _0_637 = is_monadic_comp comp  in
                         trans_G env _0_638 _0_637 app  in
                       FStar_Syntax_Util.arrow binders comp))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____4512,uu____4513) ->
             trans_F_ env e wp
         | uu____4532 -> failwith "impossible trans_F_")

and trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun h  ->
      fun is_monadic  ->
        fun wp  ->
          let mk x = FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos
             in
          if is_monadic
          then
            FStar_Syntax_Syntax.mk_Comp
              (let _0_642 =
                 let _0_641 = FStar_Syntax_Syntax.as_arg (star_type' env h)
                    in
                 let _0_640 =
                   let _0_639 = FStar_Syntax_Syntax.as_arg wp  in [_0_639]
                    in
                 _0_641 :: _0_640  in
               {
                 FStar_Syntax_Syntax.comp_typ_name =
                   FStar_Syntax_Const.effect_PURE_lid;
                 FStar_Syntax_Syntax.comp_univs =
                   [FStar_Syntax_Syntax.U_unknown];
                 FStar_Syntax_Syntax.effect_args = _0_642;
                 FStar_Syntax_Syntax.flags = []
               })
          else FStar_Syntax_Syntax.mk_Total (trans_F_ env h wp)

let n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.NoDeltaSteps;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term =
  fun env  -> fun t  -> let _0_643 = n env.env t  in star_type' env _0_643 
let star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> let _0_644 = n env.env t  in check_n env _0_644 
let trans_F :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let _0_646 = n env.env c  in
        let _0_645 = n env.env wp  in trans_F_ env _0_646 _0_645
  