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
    let binders_of_env_int nm args =
      match args with
      | (e,uu____1176)::[] ->
          let uu____1181 =
            let uu____1182 =
              let uu____1184 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____1184 in
            FStar_Reflection_Basic.embed_binders uu____1182 in
          FStar_Pervasives_Native.Some uu____1181
      | uu____1185 ->
          let uu____1189 =
            let uu____1190 = FStar_Ident.string_of_lid nm in
            let uu____1191 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____1190
              uu____1191 in
          failwith uu____1189 in
    let uu____1193 =
      let uu____1195 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1196 =
        let uu____1198 =
          mktac2 "__trytac" (fun uu____1202  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1209 =
          let uu____1211 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1214 =
            let uu____1216 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit in
            let uu____1218 =
              let uu____1220 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1221 =
                let uu____1223 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1224 =
                  let uu____1226 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1227 =
                    let uu____1229 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1230 =
                      let uu____1232 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1233 =
                        let uu____1235 =
                          mktac1 "__exact_lemma"
                            FStar_Tactics_Basic.exact_lemma
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1236 =
                          let uu____1238 =
                            mktac1 "__apply" FStar_Tactics_Basic.apply
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1239 =
                            let uu____1241 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1242 =
                              let uu____1244 =
                                mktac5 "__divide"
                                  (fun uu____1251  ->
                                     fun uu____1252  ->
                                       FStar_Tactics_Basic.divide)
                                  (fun t  -> t) (fun t  -> t)
                                  FStar_Reflection_Basic.unembed_int
                                  (unembed_tactic_0 (fun t  -> t))
                                  (unembed_tactic_0 (fun t  -> t))
                                  (FStar_Reflection_Basic.embed_pair
                                     (fun t  -> t) t_unit (fun t  -> t)
                                     t_unit) t_unit in
                              let uu____1265 =
                                let uu____1267 =
                                  mktac1 "__set_options"
                                    FStar_Tactics_Basic.set_options
                                    FStar_Reflection_Basic.unembed_string
                                    FStar_Reflection_Basic.embed_unit t_unit in
                                let uu____1268 =
                                  let uu____1270 =
                                    mktac2 "__seq" FStar_Tactics_Basic.seq
                                      (unembed_tactic_0
                                         FStar_Reflection_Basic.unembed_unit)
                                      (unembed_tactic_0
                                         FStar_Reflection_Basic.unembed_unit)
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1273 =
                                    let uu____1275 =
                                      mktac1 "__prune"
                                        FStar_Tactics_Basic.prune
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1276 =
                                      let uu____1278 =
                                        mktac1 "__addns"
                                          FStar_Tactics_Basic.addns
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1279 =
                                        let uu____1281 =
                                          mktac1 "__print"
                                            (fun x  ->
                                               FStar_Tactics_Basic.tacprint x;
                                               FStar_Tactics_Basic.ret ())
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1286 =
                                          let uu____1288 =
                                            mktac1 "__dump"
                                              FStar_Tactics_Basic.print_proof_state
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1289 =
                                            let uu____1291 =
                                              mktac1 "__dump1"
                                                FStar_Tactics_Basic.print_proof_state1
                                                FStar_Reflection_Basic.unembed_string
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1292 =
                                              let uu____1294 =
                                                mktac1 "__pointwise"
                                                  FStar_Tactics_Basic.pointwise
                                                  (unembed_tactic_0
                                                     FStar_Reflection_Basic.unembed_unit)
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1296 =
                                                let uu____1298 =
                                                  mktac0 "__trefl"
                                                    FStar_Tactics_Basic.trefl
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1299 =
                                                  let uu____1301 =
                                                    mktac0 "__later"
                                                      FStar_Tactics_Basic.later
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1302 =
                                                    let uu____1304 =
                                                      mktac0 "__flip"
                                                        FStar_Tactics_Basic.flip
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1305 =
                                                      let uu____1307 =
                                                        mktac0 "__qed"
                                                          FStar_Tactics_Basic.qed
                                                          FStar_Reflection_Basic.embed_unit
                                                          t_unit in
                                                      let uu____1308 =
                                                        let uu____1310 =
                                                          let uu____1311 =
                                                            FStar_Tactics_Embedding.pair_typ
                                                              FStar_Reflection_Data.fstar_refl_term
                                                              FStar_Reflection_Data.fstar_refl_term in
                                                          mktac1 "__cases"
                                                            FStar_Tactics_Basic.cases
                                                            FStar_Reflection_Basic.unembed_term
                                                            (FStar_Reflection_Basic.embed_pair
                                                               FStar_Reflection_Basic.embed_term
                                                               FStar_Reflection_Data.fstar_refl_term
                                                               FStar_Reflection_Basic.embed_term
                                                               FStar_Reflection_Data.fstar_refl_term)
                                                            uu____1311 in
                                                        let uu____1314 =
                                                          let uu____1316 =
                                                            mk_refl
                                                              ["Syntax";
                                                              "__binders_of_env"]
                                                              (Prims.parse_int
                                                                 "1")
                                                              binders_of_env_int in
                                                          let uu____1317 =
                                                            let uu____1319 =
                                                              mktac0
                                                                "__cur_env"
                                                                FStar_Tactics_Basic.cur_env
                                                                (FStar_Tactics_Embedding.embed_env
                                                                   ps)
                                                                FStar_Reflection_Data.fstar_refl_env in
                                                            let uu____1320 =
                                                              let uu____1322
                                                                =
                                                                mktac0
                                                                  "__cur_goal"
                                                                  FStar_Tactics_Basic.cur_goal'
                                                                  FStar_Reflection_Basic.embed_term
                                                                  FStar_Reflection_Data.fstar_refl_term in
                                                              let uu____1323
                                                                =
                                                                let uu____1325
                                                                  =
                                                                  mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                [uu____1325] in
                                                              uu____1322 ::
                                                                uu____1323 in
                                                            uu____1319 ::
                                                              uu____1320 in
                                                          uu____1316 ::
                                                            uu____1317 in
                                                        uu____1310 ::
                                                          uu____1314 in
                                                      uu____1307 ::
                                                        uu____1308 in
                                                    uu____1304 :: uu____1305 in
                                                  uu____1301 :: uu____1302 in
                                                uu____1298 :: uu____1299 in
                                              uu____1294 :: uu____1296 in
                                            uu____1291 :: uu____1292 in
                                          uu____1288 :: uu____1289 in
                                        uu____1281 :: uu____1286 in
                                      uu____1278 :: uu____1279 in
                                    uu____1275 :: uu____1276 in
                                  uu____1270 :: uu____1273 in
                                uu____1267 :: uu____1268 in
                              uu____1244 :: uu____1265 in
                            uu____1241 :: uu____1242 in
                          uu____1238 :: uu____1239 in
                        uu____1235 :: uu____1236 in
                      uu____1232 :: uu____1233 in
                    uu____1229 :: uu____1230 in
                  uu____1226 :: uu____1227 in
                uu____1223 :: uu____1224 in
              uu____1220 :: uu____1221 in
            uu____1216 :: uu____1218 in
          uu____1211 :: uu____1214 in
        uu____1198 :: uu____1209 in
      uu____1195 :: uu____1196 in
    FStar_List.append uu____1193
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1338 =
           let uu____1339 =
             let uu____1340 =
               let uu____1341 =
                 FStar_Tactics_Embedding.embed_proofstate proof_state in
               FStar_Syntax_Syntax.as_arg uu____1341 in
             [uu____1340] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1339 in
         uu____1338 FStar_Pervasives_Native.None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1348 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1355  ->
              let uu____1356 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1356) in
       FStar_Tactics_Basic.bind uu____1348
         (fun uu____1360  ->
            let result =
              let uu____1362 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1362 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1364 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1371  ->
                   let uu____1372 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1372) in
            FStar_Tactics_Basic.bind uu____1364
              (fun uu____1378  ->
                 let uu____1379 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____1379 with
                 | FStar_Util.Inl (b,ps) ->
                     let uu____1393 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1393
                       (fun uu____1396  -> FStar_Tactics_Basic.ret b)
                 | FStar_Util.Inr (msg,ps) ->
                     let uu____1403 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1403
                       (fun uu____1406  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ tau env typ =
  let uu____1433 = FStar_TypeChecker_Env.clear_expected_typ env in
  match uu____1433 with
  | (env1,uu____1441) ->
      let env2 =
        let uu___108_1445 = env1 in
        {
          FStar_TypeChecker_Env.solver =
            (uu___108_1445.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___108_1445.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___108_1445.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___108_1445.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___108_1445.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___108_1445.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___108_1445.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___108_1445.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___108_1445.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___108_1445.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___108_1445.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___108_1445.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___108_1445.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___108_1445.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___108_1445.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___108_1445.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___108_1445.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___108_1445.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___108_1445.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___108_1445.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___108_1445.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___108_1445.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___108_1445.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___108_1445.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___108_1445.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___108_1445.FStar_TypeChecker_Env.is_native_tactic)
        } in
      let uu____1446 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
      (match uu____1446 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps) in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1468,ps1) ->
                ((let uu____1471 = FStar_ST.read tacdbg in
                  if uu____1471
                  then
                    let uu____1474 = FStar_Syntax_Print.term_to_string w in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1474
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1481 = FStar_Tactics_Basic.is_irrelevant g in
                      if uu____1481
                      then
                        let uu____1482 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Util.exp_unit in
                        (if uu____1482
                         then ()
                         else
                           (let uu____1484 =
                              let uu____1485 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1485 in
                            failwith uu____1484))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___111_1488 = FStar_TypeChecker_Rel.trivial_guard in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___111_1488.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___111_1488.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___111_1488.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    } in
                  let g1 =
                    let uu____1490 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g in
                    FStar_All.pipe_right uu____1490
                      FStar_TypeChecker_Rel.resolve_implicits_lax in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                let uu____1495 =
                  let uu____1496 =
                    let uu____1499 =
                      FStar_Util.format1 "user tactic failed: %s" s in
                    (uu____1499, (typ.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____1496 in
                raise uu____1495))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1507 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1512 -> false
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
        let uu____1535 = FStar_Syntax_Util.head_and_args t in
        match uu____1535 with
        | (hd1,args) ->
            let uu____1564 =
              let uu____1572 =
                let uu____1573 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1573.FStar_Syntax_Syntax.n in
              (uu____1572, args) in
            (match uu____1564 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1586)::(tactic,uu____1588)::(assertion,uu____1590)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1629)::(tactic,uu____1631)::(assertion,uu____1633)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let uu____1667 =
                   let uu____1671 =
                     unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                       tactic in
                   run_tactic_on_typ uu____1671 e assertion in
                 (match uu____1667 with
                  | (gs,uu____1677) -> (FStar_Syntax_Util.t_true, gs))
             | uu____1681 -> (t, []))
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
          let uu____1733 =
            let uu____1737 =
              let uu____1738 = FStar_Syntax_Subst.compress t in
              uu____1738.FStar_Syntax_Syntax.n in
            match uu____1737 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1750 = traverse f pol e t1 in
                (match uu____1750 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1768 = traverse f pol e t1 in
                (match uu____1768 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1781;
                   FStar_Syntax_Syntax.pos = uu____1782;
                   FStar_Syntax_Syntax.vars = uu____1783;_},(p,uu____1785)::
                 (q,uu____1787)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let uu____1818 =
                  let uu____1822 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1822 p in
                (match uu____1818 with
                 | (p',gs1) ->
                     let uu____1830 =
                       let uu____1834 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1834 q in
                     (match uu____1830 with
                      | (q',gs2) ->
                          let uu____1842 =
                            let uu____1843 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1843.FStar_Syntax_Syntax.n in
                          (uu____1842, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1863 = traverse f pol e hd1 in
                (match uu____1863 with
                 | (hd',gs1) ->
                     let uu____1874 =
                       FStar_List.fold_right
                         (fun uu____1898  ->
                            fun uu____1899  ->
                              match (uu____1898, uu____1899) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1942 = traverse f pol e a in
                                  (match uu____1942 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1874 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2000 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2000 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2009 =
                       let uu____2017 =
                         FStar_List.map
                           (fun uu____2037  ->
                              match uu____2037 with
                              | (bv,aq) ->
                                  let uu____2047 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2047 with
                                   | (s',gs) ->
                                       (((let uu___112_2064 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___112_2064.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___112_2064.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2017 in
                     (match uu____2009 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2098 = traverse f pol e' topen in
                          (match uu____2098 with
                           | (topen',gs2) ->
                               let uu____2109 =
                                 let uu____2110 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2110.FStar_Syntax_Syntax.n in
                               (uu____2109, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____1733 with
          | (tn',gs) ->
              let t' =
                let uu___113_2126 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___113_2126.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___113_2126.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___113_2126.FStar_Syntax_Syntax.vars)
                } in
              let uu____2131 = f pol e t' in
              (match uu____2131 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let getprop:
  FStar_Tactics_Basic.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t in
      let uu____2154 = FStar_Syntax_Util.un_squash tn in
      match uu____2154 with
      | FStar_Pervasives_Native.Some t' -> FStar_Pervasives_Native.Some t'
      | FStar_Pervasives_Native.None  ->
          let uu____2168 = FStar_Syntax_Util.head_and_args tn in
          (match uu____2168 with
           | (hd1,uu____2180) ->
               let uu____2195 =
                 let uu____2196 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____2196.FStar_Syntax_Syntax.n in
               (match uu____2195 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid
                    -> FStar_Pervasives_Native.Some t
                | uu____2201 -> FStar_Pervasives_Native.None))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____2219 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____2219);
      (let uu____2223 = FStar_ST.read tacdbg in
       if uu____2223
       then
         let uu____2226 =
           let uu____2227 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2227
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2228 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2226
           uu____2228
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2244 = traverse by_tactic_interp Pos env goal in
       match uu____2244 with
       | (t',gs) ->
           ((let uu____2257 = FStar_ST.read tacdbg in
             if uu____2257
             then
               let uu____2260 =
                 let uu____2261 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2261
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2262 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2260 uu____2262
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2291  ->
                    fun g  ->
                      match uu____2291 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2316 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty in
                            match uu____2316 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2318 =
                                  let uu____2319 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2319 in
                                failwith uu____2318
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____2322 = FStar_ST.read tacdbg in
                            if uu____2322
                            then
                              let uu____2325 = FStar_Util.string_of_int n1 in
                              let uu____2326 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2325 uu____2326
                            else ());
                           (let gt' =
                              let uu____2329 =
                                let uu____2330 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____2330 in
                              FStar_TypeChecker_Util.label uu____2329
                                FStar_Range.dummyRange phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt',
                                 (g.FStar_Tactics_Basic.opts)) :: gs1))))) s
                 gs in
             let uu____2338 = s1 in
             match uu____2338 with
             | (uu____2349,gs1) ->
                 let uu____2359 =
                   let uu____2363 = FStar_Options.peek () in
                   (env, t', uu____2363) in
                 uu____2359 :: gs1)))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____2372 =
        let uu____2373 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____2373 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____2372 [FStar_Syntax_Syntax.U_zero] in
    let uu____2374 =
      let uu____2375 =
        let uu____2376 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____2377 =
          let uu____2379 = FStar_Syntax_Syntax.as_arg a in [uu____2379] in
        uu____2376 :: uu____2377 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____2375 in
    uu____2374 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____2396 =
          let uu____2400 =
            let uu____2402 = reify_tactic tau in
            unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____2402 in
          run_tactic_on_typ uu____2400 env typ in
        match uu____2396 with
        | (gs,w) ->
            (match gs with
             | [] -> w
             | uu____2407::uu____2408 ->
                 raise
                   (FStar_Errors.Error
                      ("synthesis left open goals",
                        (typ.FStar_Syntax_Syntax.pos))))