open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let t_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_unit
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____54)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____71  ->
            let uu____72 = FStar_Ident.string_of_lid nm in
            let uu____73 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____72 uu____73);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res = FStar_Tactics_Basic.run t ps1 in
        let uu____77 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        FStar_Pervasives_Native.Some uu____77))
  | uu____78 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____147)::(embedded_state,uu____149)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____174  ->
            let uu____175 = FStar_Ident.string_of_lid nm in
            let uu____176 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____175
              uu____176);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____180 = let uu____182 = unembed_b b in t uu____182 in
          FStar_Tactics_Basic.run uu____180 ps1 in
        let uu____183 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        FStar_Pervasives_Native.Some uu____183))
  | uu____184 ->
      let uu____185 =
        let uu____186 = FStar_Ident.string_of_lid nm in
        let uu____187 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____186 uu____187 in
      failwith uu____185
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____275)::(b,uu____277)::(embedded_state,uu____279)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____312  ->
            let uu____313 = FStar_Ident.string_of_lid nm in
            let uu____314 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____313
              uu____314);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____318 =
            let uu____320 = unembed_a a in
            let uu____321 = unembed_b b in t uu____320 uu____321 in
          FStar_Tactics_Basic.run uu____318 ps1 in
        let uu____322 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
        FStar_Pervasives_Native.Some uu____322))
  | uu____323 ->
      let uu____324 =
        let uu____325 = FStar_Ident.string_of_lid nm in
        let uu____326 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____325 uu____326 in
      failwith uu____324
let mk_tactic_interpretation_3 ps t unembed_a unembed_b unembed_c embed_d t_d
  nm args =
  match args with
  | (a,uu____433)::(b,uu____435)::(c,uu____437)::(embedded_state,uu____439)::[]
      ->
      (FStar_Tactics_Basic.log ps
         (fun uu____480  ->
            let uu____481 = FStar_Ident.string_of_lid nm in
            let uu____482 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____481
              uu____482);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____486 =
            let uu____488 = unembed_a a in
            let uu____489 = unembed_b b in
            let uu____490 = unembed_c c in t uu____488 uu____489 uu____490 in
          FStar_Tactics_Basic.run uu____486 ps1 in
        let uu____491 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d in
        FStar_Pervasives_Native.Some uu____491))
  | uu____492 ->
      let uu____493 =
        let uu____494 = FStar_Ident.string_of_lid nm in
        let uu____495 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____494 uu____495 in
      failwith uu____493
let mk_tactic_interpretation_5 ps t unembed_a unembed_b unembed_c unembed_d
  unembed_e embed_f t_f nm args =
  match args with
  | (a,uu____640)::(b,uu____642)::(c,uu____644)::(d,uu____646)::(e,uu____648)::
      (embedded_state,uu____650)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____707  ->
            let uu____708 = FStar_Ident.string_of_lid nm in
            let uu____709 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____708
              uu____709);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____713 =
            let uu____715 = unembed_a a in
            let uu____716 = unembed_b b in
            let uu____717 = unembed_c c in
            let uu____718 = unembed_d d in
            let uu____719 = unembed_e e in
            t uu____715 uu____716 uu____717 uu____718 uu____719 in
          FStar_Tactics_Basic.run uu____713 ps1 in
        let uu____720 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f in
        FStar_Pervasives_Native.Some uu____720))
  | uu____721 ->
      let uu____722 =
        let uu____723 = FStar_Ident.string_of_lid nm in
        let uu____724 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____723 uu____724 in
      failwith uu____722
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____735 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____735);
      {
        FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Normalize.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Normalize.interpretation =
          ((fun _rng  -> fun args  -> s.FStar_Tactics_Native.tactic ps args))
      }
let rec primitive_steps:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  fun ps  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      } in
    let native_tactics = FStar_Tactics_Native.list_all () in
    let native_tactics_steps =
      FStar_List.map (step_from_native_step ps) native_tactics in
    let mk_refl nm arity interpretation =
      let nm1 = FStar_Reflection_Data.fstar_refl_lid nm in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      } in
    let mktac0 name f e_a ta =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 ps f e_a ta) in
    let mktac1 name f u_a e_b tb =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 ps f u_a e_b tb) in
    let mktac2 name f u_a u_b e_c tc =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 ps f u_a u_b e_c tc) in
    let mktac3 name f u_a u_b u_c e_d tc =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 ps f u_a u_b u_c e_d tc) in
    let mktac5 name f u_a u_b u_c u_d u_e e_f tc =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 ps f u_a u_b u_c u_d u_e e_f tc) in
    let uu____1160 =
      let uu____1162 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1163 =
        let uu____1165 =
          mktac2 "__trytac" (fun uu____1169  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1176 =
          let uu____1178 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1181 =
            let uu____1183 =
              let uu____1184 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Reflection_Basic.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1184 in
            let uu____1189 =
              let uu____1191 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Reflection_Basic.unembed_list
                     FStar_Reflection_Basic.unembed_norm_step)
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1193 =
                let uu____1195 =
                  mktac0 "__revert" FStar_Tactics_Basic.revert
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1196 =
                  let uu____1198 =
                    mktac0 "__clear" FStar_Tactics_Basic.clear
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1199 =
                    let uu____1201 =
                      mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1202 =
                      let uu____1204 =
                        mktac0 "__smt" FStar_Tactics_Basic.smt
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1205 =
                        let uu____1207 =
                          mktac1 "__exact" FStar_Tactics_Basic.exact
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1208 =
                          let uu____1210 =
                            mktac1 "__exact_lemma"
                              FStar_Tactics_Basic.exact_lemma
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1211 =
                            let uu____1213 =
                              mktac1 "__apply" FStar_Tactics_Basic.apply
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1214 =
                              let uu____1216 =
                                mktac1 "__apply_lemma"
                                  FStar_Tactics_Basic.apply_lemma
                                  FStar_Reflection_Basic.unembed_term
                                  FStar_Reflection_Basic.embed_unit t_unit in
                              let uu____1217 =
                                let uu____1219 =
                                  mktac5 "__divide"
                                    (fun uu____1226  ->
                                       fun uu____1227  ->
                                         FStar_Tactics_Basic.divide)
                                    (fun t  -> t) (fun t  -> t)
                                    FStar_Reflection_Basic.unembed_int
                                    (unembed_tactic_0 (fun t  -> t))
                                    (unembed_tactic_0 (fun t  -> t))
                                    (FStar_Reflection_Basic.embed_pair
                                       (fun t  -> t) t_unit (fun t  -> t)
                                       t_unit) t_unit in
                                let uu____1240 =
                                  let uu____1242 =
                                    mktac1 "__set_options"
                                      FStar_Tactics_Basic.set_options
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1243 =
                                    let uu____1245 =
                                      mktac2 "__seq" FStar_Tactics_Basic.seq
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1248 =
                                      let uu____1250 =
                                        mktac1 "__prune"
                                          FStar_Tactics_Basic.prune
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1251 =
                                        let uu____1253 =
                                          mktac1 "__addns"
                                            FStar_Tactics_Basic.addns
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1254 =
                                          let uu____1256 =
                                            mktac1 "__print"
                                              (fun x  ->
                                                 FStar_Tactics_Basic.tacprint
                                                   x;
                                                 FStar_Tactics_Basic.ret ())
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1261 =
                                            let uu____1263 =
                                              mktac1 "__dump"
                                                FStar_Tactics_Basic.print_proof_state
                                                FStar_Reflection_Basic.unembed_string
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1264 =
                                              let uu____1266 =
                                                mktac1 "__dump1"
                                                  FStar_Tactics_Basic.print_proof_state1
                                                  FStar_Reflection_Basic.unembed_string
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1267 =
                                                let uu____1269 =
                                                  mktac1 "__pointwise"
                                                    FStar_Tactics_Basic.pointwise
                                                    (unembed_tactic_0
                                                       FStar_Reflection_Basic.unembed_unit)
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1271 =
                                                  let uu____1273 =
                                                    mktac0 "__trefl"
                                                      FStar_Tactics_Basic.trefl
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1274 =
                                                    let uu____1276 =
                                                      mktac0 "__later"
                                                        FStar_Tactics_Basic.later
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1277 =
                                                      let uu____1279 =
                                                        mktac0 "__dup"
                                                          FStar_Tactics_Basic.dup
                                                          FStar_Reflection_Basic.embed_unit
                                                          t_unit in
                                                      let uu____1280 =
                                                        let uu____1282 =
                                                          mktac0 "__flip"
                                                            FStar_Tactics_Basic.flip
                                                            FStar_Reflection_Basic.embed_unit
                                                            t_unit in
                                                        let uu____1283 =
                                                          let uu____1285 =
                                                            mktac0 "__qed"
                                                              FStar_Tactics_Basic.qed
                                                              FStar_Reflection_Basic.embed_unit
                                                              t_unit in
                                                          let uu____1286 =
                                                            let uu____1288 =
                                                              let uu____1289
                                                                =
                                                                FStar_Tactics_Embedding.pair_typ
                                                                  FStar_Reflection_Data.fstar_refl_term
                                                                  FStar_Reflection_Data.fstar_refl_term in
                                                              mktac1
                                                                "__cases"
                                                                FStar_Tactics_Basic.cases
                                                                FStar_Reflection_Basic.unembed_term
                                                                (FStar_Reflection_Basic.embed_pair
                                                                   FStar_Reflection_Basic.embed_term
                                                                   FStar_Reflection_Data.fstar_refl_term
                                                                   FStar_Reflection_Basic.embed_term
                                                                   FStar_Reflection_Data.fstar_refl_term)
                                                                uu____1289 in
                                                            let uu____1292 =
                                                              let uu____1294
                                                                =
                                                                mktac0
                                                                  "__cur_env"
                                                                  FStar_Tactics_Basic.cur_env
                                                                  FStar_Reflection_Basic.embed_env
                                                                  FStar_Reflection_Data.fstar_refl_env in
                                                              let uu____1295
                                                                =
                                                                let uu____1297
                                                                  =
                                                                  mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                let uu____1298
                                                                  =
                                                                  let uu____1300
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                  [uu____1300] in
                                                                uu____1297 ::
                                                                  uu____1298 in
                                                              uu____1294 ::
                                                                uu____1295 in
                                                            uu____1288 ::
                                                              uu____1292 in
                                                          uu____1285 ::
                                                            uu____1286 in
                                                        uu____1282 ::
                                                          uu____1283 in
                                                      uu____1279 ::
                                                        uu____1280 in
                                                    uu____1276 :: uu____1277 in
                                                  uu____1273 :: uu____1274 in
                                                uu____1269 :: uu____1271 in
                                              uu____1266 :: uu____1267 in
                                            uu____1263 :: uu____1264 in
                                          uu____1256 :: uu____1261 in
                                        uu____1253 :: uu____1254 in
                                      uu____1250 :: uu____1251 in
                                    uu____1245 :: uu____1248 in
                                  uu____1242 :: uu____1243 in
                                uu____1219 :: uu____1240 in
                              uu____1216 :: uu____1217 in
                            uu____1213 :: uu____1214 in
                          uu____1210 :: uu____1211 in
                        uu____1207 :: uu____1208 in
                      uu____1204 :: uu____1205 in
                    uu____1201 :: uu____1202 in
                  uu____1198 :: uu____1199 in
                uu____1195 :: uu____1196 in
              uu____1191 :: uu____1193 in
            uu____1183 :: uu____1189 in
          uu____1178 :: uu____1181 in
        uu____1165 :: uu____1176 in
      uu____1162 :: uu____1163 in
    FStar_List.append uu____1160
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1313 =
           let uu____1314 =
             let uu____1315 =
               let uu____1316 =
                 FStar_Tactics_Embedding.embed_proofstate proof_state in
               FStar_Syntax_Syntax.as_arg uu____1316 in
             [uu____1315] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1314 in
         uu____1313 FStar_Pervasives_Native.None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1323 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1330  ->
              let uu____1331 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1331) in
       FStar_Tactics_Basic.bind uu____1323
         (fun uu____1335  ->
            let result =
              let uu____1337 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1337 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1339 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1346  ->
                   let uu____1347 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1347) in
            FStar_Tactics_Basic.bind uu____1339
              (fun uu____1353  ->
                 let uu____1354 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____1354 with
                 | FStar_Util.Inl (b,ps) ->
                     let uu____1368 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1368
                       (fun uu____1371  -> FStar_Tactics_Basic.ret b)
                 | FStar_Util.Inr (msg,ps) ->
                     let uu____1378 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1378
                       (fun uu____1381  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ tau env typ =
  let uu____1408 = FStar_TypeChecker_Env.clear_expected_typ env in
  match uu____1408 with
  | (env1,uu____1416) ->
      let env2 =
        let uu___114_1420 = env1 in
        {
          FStar_TypeChecker_Env.solver =
            (uu___114_1420.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___114_1420.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___114_1420.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___114_1420.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___114_1420.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___114_1420.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___114_1420.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___114_1420.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___114_1420.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___114_1420.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___114_1420.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___114_1420.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___114_1420.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___114_1420.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___114_1420.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___114_1420.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___114_1420.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___114_1420.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___114_1420.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___114_1420.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___114_1420.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___114_1420.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___114_1420.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___114_1420.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___114_1420.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___114_1420.FStar_TypeChecker_Env.is_native_tactic)
        } in
      let uu____1421 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
      (match uu____1421 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps) in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1443,ps1) ->
                ((let uu____1446 = FStar_ST.read tacdbg in
                  if uu____1446
                  then
                    let uu____1449 = FStar_Syntax_Print.term_to_string w in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1449
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1456 = FStar_Tactics_Basic.is_irrelevant g in
                      if uu____1456
                      then
                        let uu____1457 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Util.exp_unit in
                        (if uu____1457
                         then ()
                         else
                           (let uu____1459 =
                              let uu____1460 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1460 in
                            failwith uu____1459))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___117_1463 = FStar_TypeChecker_Rel.trivial_guard in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___117_1463.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___117_1463.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___117_1463.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    } in
                  let g1 =
                    let uu____1465 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g in
                    FStar_All.pipe_right uu____1465
                      FStar_TypeChecker_Rel.resolve_implicits_lax in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                (FStar_Tactics_Basic.dump_proofstate ps1
                   "at the time of failure";
                 (let uu____1471 =
                    let uu____1472 =
                      let uu____1475 =
                        FStar_Util.format1 "user tactic failed: %s" s in
                      (uu____1475, (typ.FStar_Syntax_Syntax.pos)) in
                    FStar_Errors.Error uu____1472 in
                  raise uu____1471))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1483 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1488 -> false
let flip: pol -> pol = fun p  -> match p with | Pos  -> Neg | Neg  -> Pos
let by_tactic_interp:
  pol ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Tactics_Basic.goal Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1511 = FStar_Syntax_Util.head_and_args t in
        match uu____1511 with
        | (hd1,args) ->
            let uu____1540 =
              let uu____1548 =
                let uu____1549 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1549.FStar_Syntax_Syntax.n in
              (uu____1548, args) in
            (match uu____1540 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1562))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1609 =
                     let uu____1613 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     run_tactic_on_typ uu____1613 e assertion in
                   (match uu____1609 with
                    | (gs,uu____1619) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1653 =
                     run_tactic_on_typ FStar_Tactics_Basic.idtac e assertion in
                   (match uu____1653 with
                    | (gs,uu____1661) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | uu____1669 -> (t, []))
let rec traverse:
  (pol ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term,FStar_Tactics_Basic.goal Prims.list)
           FStar_Pervasives_Native.tuple2)
    ->
    pol ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Tactics_Basic.goal Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let uu____1721 =
            let uu____1725 =
              let uu____1726 = FStar_Syntax_Subst.compress t in
              uu____1726.FStar_Syntax_Syntax.n in
            match uu____1725 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1738 = traverse f pol e t1 in
                (match uu____1738 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1756 = traverse f pol e t1 in
                (match uu____1756 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1769;
                   FStar_Syntax_Syntax.pos = uu____1770;
                   FStar_Syntax_Syntax.vars = uu____1771;_},(p,uu____1773)::
                 (q,uu____1775)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let uu____1806 = traverse f (flip pol) e p in
                (match uu____1806 with
                 | (p',gs1) ->
                     let uu____1817 =
                       let uu____1821 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1821 q in
                     (match uu____1817 with
                      | (q',gs2) ->
                          let uu____1829 =
                            let uu____1830 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1830.FStar_Syntax_Syntax.n in
                          (uu____1829, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1850 = traverse f pol e hd1 in
                (match uu____1850 with
                 | (hd',gs1) ->
                     let uu____1861 =
                       FStar_List.fold_right
                         (fun uu____1885  ->
                            fun uu____1886  ->
                              match (uu____1885, uu____1886) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1929 = traverse f pol e a in
                                  (match uu____1929 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1861 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1987 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1987 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1996 =
                       let uu____2004 =
                         FStar_List.map
                           (fun uu____2024  ->
                              match uu____2024 with
                              | (bv,aq) ->
                                  let uu____2034 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2034 with
                                   | (s',gs) ->
                                       (((let uu___118_2051 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___118_2051.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___118_2051.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2004 in
                     (match uu____1996 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2085 = traverse f pol e' topen in
                          (match uu____2085 with
                           | (topen',gs2) ->
                               let uu____2096 =
                                 let uu____2097 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2097.FStar_Syntax_Syntax.n in
                               (uu____2096, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____1721 with
          | (tn',gs) ->
              let t' =
                let uu___119_2113 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___119_2113.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___119_2113.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_2113.FStar_Syntax_Syntax.vars)
                } in
              let uu____2118 = f pol e t' in
              (match uu____2118 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let getprop:
  FStar_Tactics_Basic.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t in
      FStar_Syntax_Util.un_squash tn
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____2158 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____2158);
      (let uu____2162 = FStar_ST.read tacdbg in
       if uu____2162
       then
         let uu____2165 =
           let uu____2166 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2166
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2167 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2165
           uu____2167
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2183 = traverse by_tactic_interp Pos env goal in
       match uu____2183 with
       | (t',gs) ->
           ((let uu____2196 = FStar_ST.read tacdbg in
             if uu____2196
             then
               let uu____2199 =
                 let uu____2200 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2200
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2201 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2199 uu____2201
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2230  ->
                    fun g  ->
                      match uu____2230 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2255 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty in
                            match uu____2255 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2257 =
                                  let uu____2258 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2258 in
                                failwith uu____2257
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____2261 = FStar_ST.read tacdbg in
                            if uu____2261
                            then
                              let uu____2264 = FStar_Util.string_of_int n1 in
                              let uu____2265 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2264 uu____2265
                            else ());
                           (let gt' =
                              let uu____2268 =
                                let uu____2269 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____2269 in
                              FStar_TypeChecker_Util.label uu____2268
                                FStar_Range.dummyRange phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt',
                                 (g.FStar_Tactics_Basic.opts)) :: gs1))))) s
                 gs in
             let uu____2277 = s1 in
             match uu____2277 with
             | (uu____2288,gs1) ->
                 let uu____2298 =
                   let uu____2302 = FStar_Options.peek () in
                   (env, t', uu____2302) in
                 uu____2298 :: gs1)))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____2311 =
        let uu____2312 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____2312 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____2311 [FStar_Syntax_Syntax.U_zero] in
    let uu____2313 =
      let uu____2314 =
        let uu____2315 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____2316 =
          let uu____2318 = FStar_Syntax_Syntax.as_arg a in [uu____2318] in
        uu____2315 :: uu____2316 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____2314 in
    uu____2313 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____2336 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.write tacdbg uu____2336);
        (let uu____2339 =
           let uu____2343 =
             let uu____2345 = reify_tactic tau in
             unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____2345 in
           run_tactic_on_typ uu____2343 env typ in
         match uu____2339 with
         | (gs,w) ->
             (match gs with
              | [] -> w
              | uu____2350::uu____2351 ->
                  raise
                    (FStar_Errors.Error
                       ("synthesis left open goals",
                         (typ.FStar_Syntax_Syntax.pos)))))