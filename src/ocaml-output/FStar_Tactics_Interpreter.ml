open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let t_unit: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_TypeChecker_Common.t_unit
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____57)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____78  ->
            let uu____79 = FStar_Ident.string_of_lid nm in
            let uu____80 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____79 uu____80);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res = FStar_Tactics_Basic.run t ps1 in
        let uu____85 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        FStar_Pervasives_Native.Some uu____85))
  | uu____86 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____159)::(embedded_state,uu____161)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____192  ->
            let uu____193 = FStar_Ident.string_of_lid nm in
            let uu____194 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____193
              uu____194);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____199 = let uu____202 = unembed_b b in t uu____202 in
          FStar_Tactics_Basic.run uu____199 ps1 in
        let uu____203 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        FStar_Pervasives_Native.Some uu____203))
  | uu____204 ->
      let uu____205 =
        let uu____206 = FStar_Ident.string_of_lid nm in
        let uu____207 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____206 uu____207 in
      failwith uu____205
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____299)::(b,uu____301)::(embedded_state,uu____303)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____344  ->
            let uu____345 = FStar_Ident.string_of_lid nm in
            let uu____346 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____345
              uu____346);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____351 =
            let uu____354 = unembed_a a in
            let uu____355 = unembed_b b in t uu____354 uu____355 in
          FStar_Tactics_Basic.run uu____351 ps1 in
        let uu____356 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
        FStar_Pervasives_Native.Some uu____356))
  | uu____357 ->
      let uu____358 =
        let uu____359 = FStar_Ident.string_of_lid nm in
        let uu____360 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____359 uu____360 in
      failwith uu____358
let mk_tactic_interpretation_3 ps t unembed_a unembed_b unembed_c embed_d t_d
  nm args =
  match args with
  | (a,uu____471)::(b,uu____473)::(c,uu____475)::(embedded_state,uu____477)::[]
      ->
      (FStar_Tactics_Basic.log ps
         (fun uu____528  ->
            let uu____529 = FStar_Ident.string_of_lid nm in
            let uu____530 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____529
              uu____530);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____535 =
            let uu____538 = unembed_a a in
            let uu____539 = unembed_b b in
            let uu____540 = unembed_c c in t uu____538 uu____539 uu____540 in
          FStar_Tactics_Basic.run uu____535 ps1 in
        let uu____541 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d in
        FStar_Pervasives_Native.Some uu____541))
  | uu____542 ->
      let uu____543 =
        let uu____544 = FStar_Ident.string_of_lid nm in
        let uu____545 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____544 uu____545 in
      failwith uu____543
let mk_tactic_interpretation_5 ps t unembed_a unembed_b unembed_c unembed_d
  unembed_e embed_f t_f nm args =
  match args with
  | (a,uu____694)::(b,uu____696)::(c,uu____698)::(d,uu____700)::(e,uu____702)::
      (embedded_state,uu____704)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____775  ->
            let uu____776 = FStar_Ident.string_of_lid nm in
            let uu____777 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____776
              uu____777);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____782 =
            let uu____785 = unembed_a a in
            let uu____786 = unembed_b b in
            let uu____787 = unembed_c c in
            let uu____788 = unembed_d d in
            let uu____789 = unembed_e e in
            t uu____785 uu____786 uu____787 uu____788 uu____789 in
          FStar_Tactics_Basic.run uu____782 ps1 in
        let uu____790 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f in
        FStar_Pervasives_Native.Some uu____790))
  | uu____791 ->
      let uu____792 =
        let uu____793 = FStar_Ident.string_of_lid nm in
        let uu____794 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____793 uu____794 in
      failwith uu____792
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____806 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____806);
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
    let uu____1248 =
      let uu____1251 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1252 =
        let uu____1255 =
          mktac2 "__trytac" (fun uu____1261  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1268 =
          let uu____1271 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1276 =
            let uu____1279 =
              let uu____1280 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Reflection_Basic.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1280 in
            let uu____1289 =
              let uu____1292 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Reflection_Basic.unembed_list
                     FStar_Reflection_Basic.unembed_norm_step)
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1295 =
                let uu____1298 =
                  mktac0 "__revert" FStar_Tactics_Basic.revert
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1299 =
                  let uu____1302 =
                    mktac0 "__clear" FStar_Tactics_Basic.clear
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1303 =
                    let uu____1306 =
                      mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1307 =
                      let uu____1310 =
                        mktac0 "__smt" FStar_Tactics_Basic.smt
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1311 =
                        let uu____1314 =
                          mktac1 "__exact" FStar_Tactics_Basic.exact
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1315 =
                          let uu____1318 =
                            mktac1 "__exact_lemma"
                              FStar_Tactics_Basic.exact_lemma
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1319 =
                            let uu____1322 =
                              mktac1 "__apply" FStar_Tactics_Basic.apply
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1323 =
                              let uu____1326 =
                                mktac1 "__apply_lemma"
                                  FStar_Tactics_Basic.apply_lemma
                                  FStar_Reflection_Basic.unembed_term
                                  FStar_Reflection_Basic.embed_unit t_unit in
                              let uu____1327 =
                                let uu____1330 =
                                  mktac5 "__divide"
                                    (fun uu____1341  ->
                                       fun uu____1342  ->
                                         FStar_Tactics_Basic.divide)
                                    (fun t  -> t) (fun t  -> t)
                                    FStar_Reflection_Basic.unembed_int
                                    (unembed_tactic_0 (fun t  -> t))
                                    (unembed_tactic_0 (fun t  -> t))
                                    (FStar_Reflection_Basic.embed_pair
                                       (fun t  -> t) t_unit (fun t  -> t)
                                       t_unit) t_unit in
                                let uu____1355 =
                                  let uu____1358 =
                                    mktac1 "__set_options"
                                      FStar_Tactics_Basic.set_options
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1359 =
                                    let uu____1362 =
                                      mktac2 "__seq" FStar_Tactics_Basic.seq
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1367 =
                                      let uu____1370 =
                                        mktac1 "__prune"
                                          FStar_Tactics_Basic.prune
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1371 =
                                        let uu____1374 =
                                          mktac1 "__addns"
                                            FStar_Tactics_Basic.addns
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1375 =
                                          let uu____1378 =
                                            mktac1 "__print"
                                              (fun x  ->
                                                 FStar_Tactics_Basic.tacprint
                                                   x;
                                                 FStar_Tactics_Basic.ret ())
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1383 =
                                            let uu____1386 =
                                              mktac1 "__dump"
                                                FStar_Tactics_Basic.print_proof_state
                                                FStar_Reflection_Basic.unembed_string
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1387 =
                                              let uu____1390 =
                                                mktac1 "__dump1"
                                                  FStar_Tactics_Basic.print_proof_state1
                                                  FStar_Reflection_Basic.unembed_string
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1391 =
                                                let uu____1394 =
                                                  mktac1 "__pointwise"
                                                    FStar_Tactics_Basic.pointwise
                                                    (unembed_tactic_0
                                                       FStar_Reflection_Basic.unembed_unit)
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1397 =
                                                  let uu____1400 =
                                                    mktac0 "__trefl"
                                                      FStar_Tactics_Basic.trefl
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1401 =
                                                    let uu____1404 =
                                                      mktac0 "__later"
                                                        FStar_Tactics_Basic.later
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1405 =
                                                      let uu____1408 =
                                                        mktac0 "__dup"
                                                          FStar_Tactics_Basic.dup
                                                          FStar_Reflection_Basic.embed_unit
                                                          t_unit in
                                                      let uu____1409 =
                                                        let uu____1412 =
                                                          mktac0 "__flip"
                                                            FStar_Tactics_Basic.flip
                                                            FStar_Reflection_Basic.embed_unit
                                                            t_unit in
                                                        let uu____1413 =
                                                          let uu____1416 =
                                                            mktac0 "__qed"
                                                              FStar_Tactics_Basic.qed
                                                              FStar_Reflection_Basic.embed_unit
                                                              t_unit in
                                                          let uu____1417 =
                                                            let uu____1420 =
                                                              let uu____1421
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
                                                                uu____1421 in
                                                            let uu____1426 =
                                                              let uu____1429
                                                                =
                                                                mktac0
                                                                  "__cur_env"
                                                                  FStar_Tactics_Basic.cur_env
                                                                  FStar_Reflection_Basic.embed_env
                                                                  FStar_Reflection_Data.fstar_refl_env in
                                                              let uu____1430
                                                                =
                                                                let uu____1433
                                                                  =
                                                                  mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                let uu____1434
                                                                  =
                                                                  let uu____1437
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                  [uu____1437] in
                                                                uu____1433 ::
                                                                  uu____1434 in
                                                              uu____1429 ::
                                                                uu____1430 in
                                                            uu____1420 ::
                                                              uu____1426 in
                                                          uu____1416 ::
                                                            uu____1417 in
                                                        uu____1412 ::
                                                          uu____1413 in
                                                      uu____1408 ::
                                                        uu____1409 in
                                                    uu____1404 :: uu____1405 in
                                                  uu____1400 :: uu____1401 in
                                                uu____1394 :: uu____1397 in
                                              uu____1390 :: uu____1391 in
                                            uu____1386 :: uu____1387 in
                                          uu____1378 :: uu____1383 in
                                        uu____1374 :: uu____1375 in
                                      uu____1370 :: uu____1371 in
                                    uu____1362 :: uu____1367 in
                                  uu____1358 :: uu____1359 in
                                uu____1330 :: uu____1355 in
                              uu____1326 :: uu____1327 in
                            uu____1322 :: uu____1323 in
                          uu____1318 :: uu____1319 in
                        uu____1314 :: uu____1315 in
                      uu____1310 :: uu____1311 in
                    uu____1306 :: uu____1307 in
                  uu____1302 :: uu____1303 in
                uu____1298 :: uu____1299 in
              uu____1292 :: uu____1295 in
            uu____1279 :: uu____1289 in
          uu____1271 :: uu____1276 in
        uu____1255 :: uu____1268 in
      uu____1251 :: uu____1252 in
    FStar_List.append uu____1248
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1450 =
           let uu____1451 =
             let uu____1452 =
               let uu____1453 =
                 FStar_Tactics_Embedding.embed_proofstate proof_state in
               FStar_Syntax_Syntax.as_arg uu____1453 in
             [uu____1452] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1451 in
         uu____1450 FStar_Pervasives_Native.None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1459 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1468  ->
              let uu____1469 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1469) in
       FStar_Tactics_Basic.bind uu____1459
         (fun uu____1473  ->
            let result =
              let uu____1475 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1475 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1478 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1487  ->
                   let uu____1488 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1488) in
            FStar_Tactics_Basic.bind uu____1478
              (fun uu____1494  ->
                 let uu____1495 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____1495 with
                 | FStar_Util.Inl (b,ps) ->
                     let uu____1520 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1520
                       (fun uu____1524  -> FStar_Tactics_Basic.ret b)
                 | FStar_Util.Inr (msg,ps) ->
                     let uu____1535 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1535
                       (fun uu____1539  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ tau env typ =
  let uu____1571 = FStar_TypeChecker_Env.clear_expected_typ env in
  match uu____1571 with
  | (env1,uu____1585) ->
      let env2 =
        let uu___114_1591 = env1 in
        {
          FStar_TypeChecker_Env.solver =
            (uu___114_1591.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___114_1591.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___114_1591.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___114_1591.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___114_1591.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___114_1591.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___114_1591.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___114_1591.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___114_1591.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___114_1591.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___114_1591.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___114_1591.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___114_1591.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___114_1591.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___114_1591.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___114_1591.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___114_1591.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___114_1591.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___114_1591.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___114_1591.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___114_1591.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___114_1591.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___114_1591.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___114_1591.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___114_1591.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___114_1591.FStar_TypeChecker_Env.is_native_tactic)
        } in
      let uu____1592 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
      (match uu____1592 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps) in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1626,ps1) ->
                ((let uu____1629 = FStar_ST.read tacdbg in
                  if uu____1629
                  then
                    let uu____1630 = FStar_Syntax_Print.term_to_string w in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1630
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1637 = FStar_Tactics_Basic.is_irrelevant g in
                      if uu____1637
                      then
                        let uu____1638 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Util.exp_unit in
                        (if uu____1638
                         then ()
                         else
                           (let uu____1640 =
                              let uu____1641 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1641 in
                            failwith uu____1640))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___117_1644 = FStar_TypeChecker_Rel.trivial_guard in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___117_1644.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___117_1644.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___117_1644.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    } in
                  let g1 =
                    let uu____1646 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g in
                    FStar_All.pipe_right uu____1646
                      FStar_TypeChecker_Rel.resolve_implicits_lax in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                (FStar_Tactics_Basic.dump_proofstate ps1
                   "at the time of failure";
                 (let uu____1653 =
                    let uu____1654 =
                      let uu____1659 =
                        FStar_Util.format1 "user tactic failed: %s" s in
                      (uu____1659, (typ.FStar_Syntax_Syntax.pos)) in
                    FStar_Errors.Error uu____1654 in
                  raise uu____1653))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1670 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1675 -> false
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
        let uu____1704 = FStar_Syntax_Util.head_and_args t in
        match uu____1704 with
        | (hd1,args) ->
            let uu____1747 =
              let uu____1760 =
                let uu____1761 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1761.FStar_Syntax_Syntax.n in
              (uu____1760, args) in
            (match uu____1747 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1780))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1849 =
                     let uu____1856 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     run_tactic_on_typ uu____1856 e assertion in
                   (match uu____1849 with
                    | (gs,uu____1866) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1918 =
                     run_tactic_on_typ FStar_Tactics_Basic.idtac e assertion in
                   (match uu____1918 with
                    | (gs,uu____1932) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | uu____1944 -> (t, []))
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
          let uu____2014 =
            let uu____2021 =
              let uu____2022 = FStar_Syntax_Subst.compress t in
              uu____2022.FStar_Syntax_Syntax.n in
            match uu____2021 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2037 = traverse f pol e t1 in
                (match uu____2037 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____2064 = traverse f pol e t1 in
                (match uu____2064 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2086;
                   FStar_Syntax_Syntax.vars = uu____2087;_},(p,uu____2089)::
                 (q,uu____2091)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let uu____2131 = traverse f (flip pol) e p in
                (match uu____2131 with
                 | (p',gs1) ->
                     let uu____2150 =
                       let uu____2157 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____2157 q in
                     (match uu____2150 with
                      | (q',gs2) ->
                          let uu____2170 =
                            let uu____2171 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____2171.FStar_Syntax_Syntax.n in
                          (uu____2170, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____2198 = traverse f pol e hd1 in
                (match uu____2198 with
                 | (hd',gs1) ->
                     let uu____2217 =
                       FStar_List.fold_right
                         (fun uu____2255  ->
                            fun uu____2256  ->
                              match (uu____2255, uu____2256) with
                              | ((a,q),(as',gs)) ->
                                  let uu____2337 = traverse f pol e a in
                                  (match uu____2337 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____2217 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2441 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2441 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2455 =
                       let uu____2470 =
                         FStar_List.map
                           (fun uu____2503  ->
                              match uu____2503 with
                              | (bv,aq) ->
                                  let uu____2520 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2520 with
                                   | (s',gs) ->
                                       (((let uu___118_2550 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___118_2550.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___118_2550.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2470 in
                     (match uu____2455 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2614 = traverse f pol e' topen in
                          (match uu____2614 with
                           | (topen',gs2) ->
                               let uu____2633 =
                                 let uu____2634 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2634.FStar_Syntax_Syntax.n in
                               (uu____2633, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2014 with
          | (tn',gs) ->
              let t' =
                let uu___119_2657 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___119_2657.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_2657.FStar_Syntax_Syntax.vars)
                } in
              let uu____2658 = f pol e t' in
              (match uu____2658 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let getprop:
  FStar_Tactics_Basic.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option
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
      (let uu____2717 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____2717);
      (let uu____2719 = FStar_ST.read tacdbg in
       if uu____2719
       then
         let uu____2720 =
           let uu____2721 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2721
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2722 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2720
           uu____2722
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2751 = traverse by_tactic_interp Pos env goal in
       match uu____2751 with
       | (t',gs) ->
           ((let uu____2773 = FStar_ST.read tacdbg in
             if uu____2773
             then
               let uu____2774 =
                 let uu____2775 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2775
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2776 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2774 uu____2776
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2823  ->
                    fun g  ->
                      match uu____2823 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2868 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty in
                            match uu____2868 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2871 =
                                  let uu____2872 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2872 in
                                failwith uu____2871
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____2875 = FStar_ST.read tacdbg in
                            if uu____2875
                            then
                              let uu____2876 = FStar_Util.string_of_int n1 in
                              let uu____2877 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2876 uu____2877
                            else ());
                           (let gt' =
                              let uu____2880 =
                                let uu____2881 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____2881 in
                              FStar_TypeChecker_Util.label uu____2880
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt',
                                 (g.FStar_Tactics_Basic.opts)) :: gs1))))) s
                 gs in
             let uu____2896 = s1 in
             match uu____2896 with
             | (uu____2917,gs1) ->
                 let uu____2935 =
                   let uu____2942 = FStar_Options.peek () in
                   (env, t', uu____2942) in
                 uu____2935 :: gs1)))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____2954 =
        let uu____2955 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____2955 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____2954 [FStar_Syntax_Syntax.U_zero] in
    let uu____2956 =
      let uu____2957 =
        let uu____2958 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____2959 =
          let uu____2962 = FStar_Syntax_Syntax.as_arg a in [uu____2962] in
        uu____2958 :: uu____2959 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____2957 in
    uu____2956 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____2978 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.write tacdbg uu____2978);
        (let uu____2979 =
           let uu____2986 =
             let uu____2989 = reify_tactic tau in
             unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____2989 in
           run_tactic_on_typ uu____2986 env typ in
         match uu____2979 with
         | (gs,w) ->
             (match gs with
              | [] -> w
              | uu____2996::uu____2997 ->
                  raise
                    (FStar_Errors.Error
                       ("synthesis left open goals",
                         (typ.FStar_Syntax_Syntax.pos)))))