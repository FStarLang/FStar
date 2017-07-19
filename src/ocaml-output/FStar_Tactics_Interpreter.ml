open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let t_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_unit
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____59)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____88  ->
            let uu____89 = FStar_Ident.string_of_lid nm in
            let uu____90 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____89 uu____90);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res = FStar_Tactics_Basic.run t ps1 in
        let uu____95 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        FStar_Pervasives_Native.Some uu____95))
  | uu____96 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____169)::(embedded_state,uu____171)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____216  ->
            let uu____217 = FStar_Ident.string_of_lid nm in
            let uu____218 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____217
              uu____218);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____223 = let uu____226 = unembed_b b in t uu____226 in
          FStar_Tactics_Basic.run uu____223 ps1 in
        let uu____227 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        FStar_Pervasives_Native.Some uu____227))
  | uu____228 ->
      let uu____229 =
        let uu____230 = FStar_Ident.string_of_lid nm in
        let uu____231 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____230 uu____231 in
      failwith uu____229
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____323)::(b,uu____325)::(embedded_state,uu____327)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____388  ->
            let uu____389 = FStar_Ident.string_of_lid nm in
            let uu____390 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____389
              uu____390);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____395 =
            let uu____398 = unembed_a a in
            let uu____399 = unembed_b b in t uu____398 uu____399 in
          FStar_Tactics_Basic.run uu____395 ps1 in
        let uu____400 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
        FStar_Pervasives_Native.Some uu____400))
  | uu____401 ->
      let uu____402 =
        let uu____403 = FStar_Ident.string_of_lid nm in
        let uu____404 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____403 uu____404 in
      failwith uu____402
let mk_tactic_interpretation_3 ps t unembed_a unembed_b unembed_c embed_d t_d
  nm args =
  match args with
  | (a,uu____515)::(b,uu____517)::(c,uu____519)::(embedded_state,uu____521)::[]
      ->
      (FStar_Tactics_Basic.log ps
         (fun uu____598  ->
            let uu____599 = FStar_Ident.string_of_lid nm in
            let uu____600 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____599
              uu____600);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____605 =
            let uu____608 = unembed_a a in
            let uu____609 = unembed_b b in
            let uu____610 = unembed_c c in t uu____608 uu____609 uu____610 in
          FStar_Tactics_Basic.run uu____605 ps1 in
        let uu____611 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d in
        FStar_Pervasives_Native.Some uu____611))
  | uu____612 ->
      let uu____613 =
        let uu____614 = FStar_Ident.string_of_lid nm in
        let uu____615 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____614 uu____615 in
      failwith uu____613
let mk_tactic_interpretation_5 ps t unembed_a unembed_b unembed_c unembed_d
  unembed_e embed_f t_f nm args =
  match args with
  | (a,uu____764)::(b,uu____766)::(c,uu____768)::(d,uu____770)::(e,uu____772)::
      (embedded_state,uu____774)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____883  ->
            let uu____884 = FStar_Ident.string_of_lid nm in
            let uu____885 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____884
              uu____885);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____890 =
            let uu____893 = unembed_a a in
            let uu____894 = unembed_b b in
            let uu____895 = unembed_c c in
            let uu____896 = unembed_d d in
            let uu____897 = unembed_e e in
            t uu____893 uu____894 uu____895 uu____896 uu____897 in
          FStar_Tactics_Basic.run uu____890 ps1 in
        let uu____898 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f in
        FStar_Pervasives_Native.Some uu____898))
  | uu____899 ->
      let uu____900 =
        let uu____901 = FStar_Ident.string_of_lid nm in
        let uu____902 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____901 uu____902 in
      failwith uu____900
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____914 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____914);
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
    let uu____1356 =
      let uu____1359 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1360 =
        let uu____1363 =
          mktac2 "__trytac" (fun uu____1369  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1376 =
          let uu____1379 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1384 =
            let uu____1387 =
              let uu____1388 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Reflection_Basic.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1388 in
            let uu____1397 =
              let uu____1400 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Reflection_Basic.unembed_list
                     FStar_Reflection_Basic.unembed_norm_step)
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1403 =
                let uu____1406 =
                  mktac0 "__revert" FStar_Tactics_Basic.revert
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1407 =
                  let uu____1410 =
                    mktac0 "__clear" FStar_Tactics_Basic.clear
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1411 =
                    let uu____1414 =
                      mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1415 =
                      let uu____1418 =
                        mktac0 "__smt" FStar_Tactics_Basic.smt
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1419 =
                        let uu____1422 =
                          mktac1 "__exact" FStar_Tactics_Basic.exact
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1423 =
                          let uu____1426 =
                            mktac1 "__exact_lemma"
                              FStar_Tactics_Basic.exact_lemma
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1427 =
                            let uu____1430 =
                              mktac1 "__apply" FStar_Tactics_Basic.apply
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1431 =
                              let uu____1434 =
                                mktac1 "__apply_lemma"
                                  FStar_Tactics_Basic.apply_lemma
                                  FStar_Reflection_Basic.unembed_term
                                  FStar_Reflection_Basic.embed_unit t_unit in
                              let uu____1435 =
                                let uu____1438 =
                                  mktac5 "__divide"
                                    (fun uu____1449  ->
                                       fun uu____1450  ->
                                         FStar_Tactics_Basic.divide)
                                    (fun t  -> t) (fun t  -> t)
                                    FStar_Reflection_Basic.unembed_int
                                    (unembed_tactic_0 (fun t  -> t))
                                    (unembed_tactic_0 (fun t  -> t))
                                    (FStar_Reflection_Basic.embed_pair
                                       (fun t  -> t) t_unit (fun t  -> t)
                                       t_unit) t_unit in
                                let uu____1463 =
                                  let uu____1466 =
                                    mktac1 "__set_options"
                                      FStar_Tactics_Basic.set_options
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1467 =
                                    let uu____1470 =
                                      mktac2 "__seq" FStar_Tactics_Basic.seq
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1475 =
                                      let uu____1478 =
                                        mktac1 "__prune"
                                          FStar_Tactics_Basic.prune
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1479 =
                                        let uu____1482 =
                                          mktac1 "__addns"
                                            FStar_Tactics_Basic.addns
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1483 =
                                          let uu____1486 =
                                            mktac1 "__print"
                                              (fun x  ->
                                                 FStar_Tactics_Basic.tacprint
                                                   x;
                                                 FStar_Tactics_Basic.ret ())
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1491 =
                                            let uu____1494 =
                                              mktac1 "__dump"
                                                FStar_Tactics_Basic.print_proof_state
                                                FStar_Reflection_Basic.unembed_string
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1495 =
                                              let uu____1498 =
                                                mktac1 "__dump1"
                                                  FStar_Tactics_Basic.print_proof_state1
                                                  FStar_Reflection_Basic.unembed_string
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1499 =
                                                let uu____1502 =
                                                  mktac1 "__pointwise"
                                                    FStar_Tactics_Basic.pointwise
                                                    (unembed_tactic_0
                                                       FStar_Reflection_Basic.unembed_unit)
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1505 =
                                                  let uu____1508 =
                                                    mktac0 "__trefl"
                                                      FStar_Tactics_Basic.trefl
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1509 =
                                                    let uu____1512 =
                                                      mktac0 "__later"
                                                        FStar_Tactics_Basic.later
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1513 =
                                                      let uu____1516 =
                                                        mktac0 "__dup"
                                                          FStar_Tactics_Basic.dup
                                                          FStar_Reflection_Basic.embed_unit
                                                          t_unit in
                                                      let uu____1517 =
                                                        let uu____1520 =
                                                          mktac0 "__flip"
                                                            FStar_Tactics_Basic.flip
                                                            FStar_Reflection_Basic.embed_unit
                                                            t_unit in
                                                        let uu____1521 =
                                                          let uu____1524 =
                                                            mktac0 "__qed"
                                                              FStar_Tactics_Basic.qed
                                                              FStar_Reflection_Basic.embed_unit
                                                              t_unit in
                                                          let uu____1525 =
                                                            let uu____1528 =
                                                              let uu____1529
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
                                                                uu____1529 in
                                                            let uu____1534 =
                                                              let uu____1537
                                                                =
                                                                mktac0
                                                                  "__cur_env"
                                                                  FStar_Tactics_Basic.cur_env
                                                                  FStar_Reflection_Basic.embed_env
                                                                  FStar_Reflection_Data.fstar_refl_env in
                                                              let uu____1538
                                                                =
                                                                let uu____1541
                                                                  =
                                                                  mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                let uu____1542
                                                                  =
                                                                  let uu____1545
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                  [uu____1545] in
                                                                uu____1541 ::
                                                                  uu____1542 in
                                                              uu____1537 ::
                                                                uu____1538 in
                                                            uu____1528 ::
                                                              uu____1534 in
                                                          uu____1524 ::
                                                            uu____1525 in
                                                        uu____1520 ::
                                                          uu____1521 in
                                                      uu____1516 ::
                                                        uu____1517 in
                                                    uu____1512 :: uu____1513 in
                                                  uu____1508 :: uu____1509 in
                                                uu____1502 :: uu____1505 in
                                              uu____1498 :: uu____1499 in
                                            uu____1494 :: uu____1495 in
                                          uu____1486 :: uu____1491 in
                                        uu____1482 :: uu____1483 in
                                      uu____1478 :: uu____1479 in
                                    uu____1470 :: uu____1475 in
                                  uu____1466 :: uu____1467 in
                                uu____1438 :: uu____1463 in
                              uu____1434 :: uu____1435 in
                            uu____1430 :: uu____1431 in
                          uu____1426 :: uu____1427 in
                        uu____1422 :: uu____1423 in
                      uu____1418 :: uu____1419 in
                    uu____1414 :: uu____1415 in
                  uu____1410 :: uu____1411 in
                uu____1406 :: uu____1407 in
              uu____1400 :: uu____1403 in
            uu____1387 :: uu____1397 in
          uu____1379 :: uu____1384 in
        uu____1363 :: uu____1376 in
      uu____1359 :: uu____1360 in
    FStar_List.append uu____1356
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1560 =
           let uu____1561 =
             let uu____1562 =
               let uu____1563 =
                 FStar_Tactics_Embedding.embed_proofstate proof_state in
               FStar_Syntax_Syntax.as_arg uu____1563 in
             [uu____1562] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1561 in
         uu____1560 FStar_Pervasives_Native.None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1569 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1578  ->
              let uu____1579 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1579) in
       FStar_Tactics_Basic.bind uu____1569
         (fun uu____1583  ->
            let result =
              let uu____1585 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1585 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1588 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1597  ->
                   let uu____1598 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1598) in
            FStar_Tactics_Basic.bind uu____1588
              (fun uu____1604  ->
                 let uu____1605 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____1605 with
                 | FStar_Util.Inl (b,ps) ->
                     let uu____1630 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1630
                       (fun uu____1634  -> FStar_Tactics_Basic.ret b)
                 | FStar_Util.Inr (msg,ps) ->
                     let uu____1645 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1645
                       (fun uu____1649  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ tau env typ =
  let uu____1681 = FStar_TypeChecker_Env.clear_expected_typ env in
  match uu____1681 with
  | (env1,uu____1695) ->
      let env2 =
        let uu___114_1701 = env1 in
        {
          FStar_TypeChecker_Env.solver =
            (uu___114_1701.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___114_1701.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___114_1701.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___114_1701.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___114_1701.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___114_1701.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___114_1701.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___114_1701.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___114_1701.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___114_1701.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___114_1701.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___114_1701.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___114_1701.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___114_1701.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___114_1701.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___114_1701.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___114_1701.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___114_1701.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___114_1701.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___114_1701.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___114_1701.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___114_1701.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___114_1701.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___114_1701.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___114_1701.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___114_1701.FStar_TypeChecker_Env.is_native_tactic)
        } in
      let uu____1702 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
      (match uu____1702 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps) in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1736,ps1) ->
                ((let uu____1739 = FStar_ST.read tacdbg in
                  if uu____1739
                  then
                    let uu____1740 = FStar_Syntax_Print.term_to_string w in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1740
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1747 = FStar_Tactics_Basic.is_irrelevant g in
                      if uu____1747
                      then
                        let uu____1748 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Util.exp_unit in
                        (if uu____1748
                         then ()
                         else
                           (let uu____1750 =
                              let uu____1751 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1751 in
                            failwith uu____1750))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___117_1754 = FStar_TypeChecker_Rel.trivial_guard in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___117_1754.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___117_1754.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___117_1754.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    } in
                  let g1 =
                    let uu____1756 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g in
                    FStar_All.pipe_right uu____1756
                      FStar_TypeChecker_Rel.resolve_implicits_lax in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                (FStar_Tactics_Basic.dump_proofstate ps1
                   "at the time of failure";
                 (let uu____1763 =
                    let uu____1764 =
                      let uu____1769 =
                        FStar_Util.format1 "user tactic failed: %s" s in
                      (uu____1769, (typ.FStar_Syntax_Syntax.pos)) in
                    FStar_Errors.Error uu____1764 in
                  raise uu____1763))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1780 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1785 -> false
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
        let uu____1814 = FStar_Syntax_Util.head_and_args t in
        match uu____1814 with
        | (hd1,args) ->
            let uu____1869 =
              let uu____1884 =
                let uu____1885 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1885.FStar_Syntax_Syntax.n in
              (uu____1884, args) in
            (match uu____1869 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1908))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1999 =
                     let uu____2006 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     run_tactic_on_typ uu____2006 e assertion in
                   (match uu____1999 with
                    | (gs,uu____2016) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2080 =
                     run_tactic_on_typ FStar_Tactics_Basic.idtac e assertion in
                   (match uu____2080 with
                    | (gs,uu____2094) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | uu____2108 -> (t, []))
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
          let uu____2180 =
            let uu____2187 =
              let uu____2188 = FStar_Syntax_Subst.compress t in
              uu____2188.FStar_Syntax_Syntax.n in
            match uu____2187 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2209 = traverse f pol e t1 in
                (match uu____2209 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____2240 = traverse f pol e t1 in
                (match uu____2240 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____2262;
                   FStar_Syntax_Syntax.pos = uu____2263;
                   FStar_Syntax_Syntax.vars = uu____2264;_},(p,uu____2266)::
                 (q,uu____2268)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let uu____2328 = traverse f (flip pol) e p in
                (match uu____2328 with
                 | (p',gs1) ->
                     let uu____2347 =
                       let uu____2354 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____2354 q in
                     (match uu____2347 with
                      | (q',gs2) ->
                          let uu____2367 =
                            let uu____2368 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____2368.FStar_Syntax_Syntax.n in
                          (uu____2367, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____2405 = traverse f pol e hd1 in
                (match uu____2405 with
                 | (hd',gs1) ->
                     let uu____2424 =
                       FStar_List.fold_right
                         (fun uu____2462  ->
                            fun uu____2463  ->
                              match (uu____2462, uu____2463) with
                              | ((a,q),(as',gs)) ->
                                  let uu____2544 = traverse f pol e a in
                                  (match uu____2544 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____2424 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2652 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2652 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2666 =
                       let uu____2681 =
                         FStar_List.map
                           (fun uu____2714  ->
                              match uu____2714 with
                              | (bv,aq) ->
                                  let uu____2731 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2731 with
                                   | (s',gs) ->
                                       (((let uu___118_2761 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___118_2761.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___118_2761.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2681 in
                     (match uu____2666 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2825 = traverse f pol e' topen in
                          (match uu____2825 with
                           | (topen',gs2) ->
                               let uu____2844 =
                                 let uu____2845 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2845.FStar_Syntax_Syntax.n in
                               (uu____2844, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2180 with
          | (tn',gs) ->
              let t' =
                let uu___119_2872 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___119_2872.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___119_2872.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_2872.FStar_Syntax_Syntax.vars)
                } in
              let uu____2873 = f pol e t' in
              (match uu____2873 with
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
      (let uu____2932 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____2932);
      (let uu____2934 = FStar_ST.read tacdbg in
       if uu____2934
       then
         let uu____2935 =
           let uu____2936 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2936
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2937 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2935
           uu____2937
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2966 = traverse by_tactic_interp Pos env goal in
       match uu____2966 with
       | (t',gs) ->
           ((let uu____2988 = FStar_ST.read tacdbg in
             if uu____2988
             then
               let uu____2989 =
                 let uu____2990 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2990
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2991 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2989 uu____2991
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3038  ->
                    fun g  ->
                      match uu____3038 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3083 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty in
                            match uu____3083 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3086 =
                                  let uu____3087 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____3087 in
                                failwith uu____3086
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____3090 = FStar_ST.read tacdbg in
                            if uu____3090
                            then
                              let uu____3091 = FStar_Util.string_of_int n1 in
                              let uu____3092 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3091 uu____3092
                            else ());
                           (let gt' =
                              let uu____3095 =
                                let uu____3096 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____3096 in
                              FStar_TypeChecker_Util.label uu____3095
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt',
                                 (g.FStar_Tactics_Basic.opts)) :: gs1))))) s
                 gs in
             let uu____3111 = s1 in
             match uu____3111 with
             | (uu____3132,gs1) ->
                 let uu____3150 =
                   let uu____3157 = FStar_Options.peek () in
                   (env, t', uu____3157) in
                 uu____3150 :: gs1)))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____3169 =
        let uu____3170 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____3170 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3169 [FStar_Syntax_Syntax.U_zero] in
    let uu____3171 =
      let uu____3172 =
        let uu____3173 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____3174 =
          let uu____3177 = FStar_Syntax_Syntax.as_arg a in [uu____3177] in
        uu____3173 :: uu____3174 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3172 in
    uu____3171 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____3193 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.write tacdbg uu____3193);
        (let uu____3194 =
           let uu____3201 =
             let uu____3204 = reify_tactic tau in
             unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____3204 in
           run_tactic_on_typ uu____3201 env typ in
         match uu____3194 with
         | (gs,w) ->
             (match gs with
              | [] -> w
              | uu____3211::uu____3212 ->
                  raise
                    (FStar_Errors.Error
                       ("synthesis left open goals",
                         (typ.FStar_Syntax_Syntax.pos)))))