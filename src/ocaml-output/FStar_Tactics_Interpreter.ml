open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let t_unit: FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax =
  FStar_TypeChecker_Common.t_unit
let mk_tactic_interpretation_0:
  'a .
    FStar_Tactics_Basic.proofstate ->
      'a FStar_Tactics_Basic.tac ->
        ('a -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun t  ->
      fun embed_a  ->
        fun t_a  ->
          fun nm  ->
            fun args  ->
              match args with
              | (embedded_state,uu____63)::[] ->
                  (FStar_Tactics_Basic.log ps
                     (fun uu____84  ->
                        let uu____85 = FStar_Ident.string_of_lid nm in
                        let uu____86 = FStar_Syntax_Print.args_to_string args in
                        FStar_Util.print2 "Reached %s, args are: %s\n"
                          uu____85 uu____86);
                   (let ps1 =
                      FStar_Tactics_Embedding.unembed_proofstate ps
                        embedded_state in
                    let res = FStar_Tactics_Basic.run t ps1 in
                    let uu____91 =
                      FStar_Tactics_Embedding.embed_result ps1 res embed_a
                        t_a in
                    FStar_Pervasives_Native.Some uu____91))
              | uu____92 ->
                  failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1:
  'a 'b .
    FStar_Tactics_Basic.proofstate ->
      ('b -> 'a FStar_Tactics_Basic.tac) ->
        (FStar_Syntax_Syntax.term -> 'b) ->
          ('a -> FStar_Syntax_Syntax.term) ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun t  ->
      fun unembed_b  ->
        fun embed_a  ->
          fun t_a  ->
            fun nm  ->
              fun args  ->
                match args with
                | (b,uu____165)::(embedded_state,uu____167)::[] ->
                    (FStar_Tactics_Basic.log ps
                       (fun uu____198  ->
                          let uu____199 = FStar_Ident.string_of_lid nm in
                          let uu____200 =
                            FStar_Syntax_Print.term_to_string embedded_state in
                          FStar_Util.print2 "Reached %s, goals are: %s\n"
                            uu____199 uu____200);
                     (let ps1 =
                        FStar_Tactics_Embedding.unembed_proofstate ps
                          embedded_state in
                      let res =
                        let uu____205 =
                          let uu____208 = unembed_b b in t uu____208 in
                        FStar_Tactics_Basic.run uu____205 ps1 in
                      let uu____209 =
                        FStar_Tactics_Embedding.embed_result ps1 res embed_a
                          t_a in
                      FStar_Pervasives_Native.Some uu____209))
                | uu____210 ->
                    let uu____211 =
                      let uu____212 = FStar_Ident.string_of_lid nm in
                      let uu____213 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____212 uu____213 in
                    failwith uu____211
let mk_tactic_interpretation_2:
  'a 'b 'c .
    FStar_Tactics_Basic.proofstate ->
      ('a -> 'b -> 'c FStar_Tactics_Basic.tac) ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          (FStar_Syntax_Syntax.term -> 'b) ->
            ('c -> FStar_Syntax_Syntax.term) ->
              FStar_Syntax_Syntax.typ ->
                FStar_Ident.lid ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun embed_c  ->
            fun t_c  ->
              fun nm  ->
                fun args  ->
                  match args with
                  | (a,uu____305)::(b,uu____307)::(embedded_state,uu____309)::[]
                      ->
                      (FStar_Tactics_Basic.log ps
                         (fun uu____350  ->
                            let uu____351 = FStar_Ident.string_of_lid nm in
                            let uu____352 =
                              FStar_Syntax_Print.term_to_string
                                embedded_state in
                            FStar_Util.print2 "Reached %s, goals are: %s\n"
                              uu____351 uu____352);
                       (let ps1 =
                          FStar_Tactics_Embedding.unembed_proofstate ps
                            embedded_state in
                        let res =
                          let uu____357 =
                            let uu____360 = unembed_a a in
                            let uu____361 = unembed_b b in
                            t uu____360 uu____361 in
                          FStar_Tactics_Basic.run uu____357 ps1 in
                        let uu____362 =
                          FStar_Tactics_Embedding.embed_result ps1 res
                            embed_c t_c in
                        FStar_Pervasives_Native.Some uu____362))
                  | uu____363 ->
                      let uu____364 =
                        let uu____365 = FStar_Ident.string_of_lid nm in
                        let uu____366 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____365 uu____366 in
                      failwith uu____364
let mk_tactic_interpretation_3:
  'a 'b 'c 'd .
    FStar_Tactics_Basic.proofstate ->
      ('a -> 'b -> 'c -> 'd FStar_Tactics_Basic.tac) ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          (FStar_Syntax_Syntax.term -> 'b) ->
            (FStar_Syntax_Syntax.term -> 'c) ->
              ('d -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.typ ->
                  FStar_Ident.lid ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun unembed_c  ->
            fun embed_d  ->
              fun t_d  ->
                fun nm  ->
                  fun args  ->
                    match args with
                    | (a,uu____477)::(b,uu____479)::(c,uu____481)::(embedded_state,uu____483)::[]
                        ->
                        (FStar_Tactics_Basic.log ps
                           (fun uu____534  ->
                              let uu____535 = FStar_Ident.string_of_lid nm in
                              let uu____536 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____535 uu____536);
                         (let ps1 =
                            FStar_Tactics_Embedding.unembed_proofstate ps
                              embedded_state in
                          let res =
                            let uu____541 =
                              let uu____544 = unembed_a a in
                              let uu____545 = unembed_b b in
                              let uu____546 = unembed_c c in
                              t uu____544 uu____545 uu____546 in
                            FStar_Tactics_Basic.run uu____541 ps1 in
                          let uu____547 =
                            FStar_Tactics_Embedding.embed_result ps1 res
                              embed_d t_d in
                          FStar_Pervasives_Native.Some uu____547))
                    | uu____548 ->
                        let uu____549 =
                          let uu____550 = FStar_Ident.string_of_lid nm in
                          let uu____551 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____550 uu____551 in
                        failwith uu____549
let mk_tactic_interpretation_5:
  'a 'b 'c 'd 'e 'f .
    FStar_Tactics_Basic.proofstate ->
      ('a -> 'b -> 'c -> 'd -> 'e -> 'f FStar_Tactics_Basic.tac) ->
        (FStar_Syntax_Syntax.term -> 'a) ->
          (FStar_Syntax_Syntax.term -> 'b) ->
            (FStar_Syntax_Syntax.term -> 'c) ->
              (FStar_Syntax_Syntax.term -> 'd) ->
                (FStar_Syntax_Syntax.term -> 'e) ->
                  ('f -> FStar_Syntax_Syntax.term) ->
                    FStar_Syntax_Syntax.typ ->
                      FStar_Ident.lid ->
                        FStar_Syntax_Syntax.args ->
                          FStar_Syntax_Syntax.term
                            FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun t  ->
      fun unembed_a  ->
        fun unembed_b  ->
          fun unembed_c  ->
            fun unembed_d  ->
              fun unembed_e  ->
                fun embed_f  ->
                  fun t_f  ->
                    fun nm  ->
                      fun args  ->
                        match args with
                        | (a,uu____700)::(b,uu____702)::(c,uu____704)::
                            (d,uu____706)::(e,uu____708)::(embedded_state,uu____710)::[]
                            ->
                            (FStar_Tactics_Basic.log ps
                               (fun uu____781  ->
                                  let uu____782 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____783 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____782
                                    uu____783);
                             (let ps1 =
                                FStar_Tactics_Embedding.unembed_proofstate ps
                                  embedded_state in
                              let res =
                                let uu____788 =
                                  let uu____791 = unembed_a a in
                                  let uu____792 = unembed_b b in
                                  let uu____793 = unembed_c c in
                                  let uu____794 = unembed_d d in
                                  let uu____795 = unembed_e e in
                                  t uu____791 uu____792 uu____793 uu____794
                                    uu____795 in
                                FStar_Tactics_Basic.run uu____788 ps1 in
                              let uu____796 =
                                FStar_Tactics_Embedding.embed_result ps1 res
                                  embed_f t_f in
                              FStar_Pervasives_Native.Some uu____796))
                        | uu____797 ->
                            let uu____798 =
                              let uu____799 = FStar_Ident.string_of_lid nm in
                              let uu____800 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____799 uu____800 in
                            failwith uu____798
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____812 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____812);
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
    let uu____1254 =
      let uu____1257 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1258 =
        let uu____1261 =
          mktac2 "__trytac" (fun uu____1267  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1274 =
          let uu____1277 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1282 =
            let uu____1285 =
              let uu____1286 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Reflection_Basic.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1286 in
            let uu____1295 =
              let uu____1298 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Reflection_Basic.unembed_list
                     FStar_Reflection_Basic.unembed_norm_step)
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1301 =
                let uu____1304 =
                  mktac0 "__revert" FStar_Tactics_Basic.revert
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1305 =
                  let uu____1308 =
                    mktac0 "__clear" FStar_Tactics_Basic.clear
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1309 =
                    let uu____1312 =
                      mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1313 =
                      let uu____1316 =
                        mktac0 "__smt" FStar_Tactics_Basic.smt
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1317 =
                        let uu____1320 =
                          mktac1 "__exact" FStar_Tactics_Basic.exact
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1321 =
                          let uu____1324 =
                            mktac1 "__exact_lemma"
                              FStar_Tactics_Basic.exact_lemma
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1325 =
                            let uu____1328 =
                              mktac1 "__apply" FStar_Tactics_Basic.apply
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1329 =
                              let uu____1332 =
                                mktac1 "__apply_lemma"
                                  FStar_Tactics_Basic.apply_lemma
                                  FStar_Reflection_Basic.unembed_term
                                  FStar_Reflection_Basic.embed_unit t_unit in
                              let uu____1333 =
                                let uu____1336 =
                                  mktac5 "__divide"
                                    (fun uu____1347  ->
                                       fun uu____1348  ->
                                         FStar_Tactics_Basic.divide)
                                    (fun t  -> t) (fun t  -> t)
                                    FStar_Reflection_Basic.unembed_int
                                    (unembed_tactic_0 (fun t  -> t))
                                    (unembed_tactic_0 (fun t  -> t))
                                    (FStar_Reflection_Basic.embed_pair
                                       (fun t  -> t) t_unit (fun t  -> t)
                                       t_unit) t_unit in
                                let uu____1361 =
                                  let uu____1364 =
                                    mktac1 "__set_options"
                                      FStar_Tactics_Basic.set_options
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1365 =
                                    let uu____1368 =
                                      mktac2 "__seq" FStar_Tactics_Basic.seq
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        (unembed_tactic_0
                                           FStar_Reflection_Basic.unembed_unit)
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1373 =
                                      let uu____1376 =
                                        mktac1 "__prune"
                                          FStar_Tactics_Basic.prune
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1377 =
                                        let uu____1380 =
                                          mktac1 "__addns"
                                            FStar_Tactics_Basic.addns
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1381 =
                                          let uu____1384 =
                                            mktac1 "__print"
                                              (fun x  ->
                                                 FStar_Tactics_Basic.tacprint
                                                   x;
                                                 FStar_Tactics_Basic.ret ())
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1389 =
                                            let uu____1392 =
                                              mktac1 "__dump"
                                                FStar_Tactics_Basic.print_proof_state
                                                FStar_Reflection_Basic.unembed_string
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1393 =
                                              let uu____1396 =
                                                mktac1 "__dump1"
                                                  FStar_Tactics_Basic.print_proof_state1
                                                  FStar_Reflection_Basic.unembed_string
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1397 =
                                                let uu____1400 =
                                                  mktac1 "__pointwise"
                                                    FStar_Tactics_Basic.pointwise
                                                    (unembed_tactic_0
                                                       FStar_Reflection_Basic.unembed_unit)
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1403 =
                                                  let uu____1406 =
                                                    mktac0 "__trefl"
                                                      FStar_Tactics_Basic.trefl
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1407 =
                                                    let uu____1410 =
                                                      mktac0 "__later"
                                                        FStar_Tactics_Basic.later
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1411 =
                                                      let uu____1414 =
                                                        mktac0 "__dup"
                                                          FStar_Tactics_Basic.dup
                                                          FStar_Reflection_Basic.embed_unit
                                                          t_unit in
                                                      let uu____1415 =
                                                        let uu____1418 =
                                                          mktac0 "__flip"
                                                            FStar_Tactics_Basic.flip
                                                            FStar_Reflection_Basic.embed_unit
                                                            t_unit in
                                                        let uu____1419 =
                                                          let uu____1422 =
                                                            mktac0 "__qed"
                                                              FStar_Tactics_Basic.qed
                                                              FStar_Reflection_Basic.embed_unit
                                                              t_unit in
                                                          let uu____1423 =
                                                            let uu____1426 =
                                                              let uu____1427
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
                                                                uu____1427 in
                                                            let uu____1432 =
                                                              let uu____1435
                                                                =
                                                                mktac0
                                                                  "__cur_env"
                                                                  FStar_Tactics_Basic.cur_env
                                                                  FStar_Reflection_Basic.embed_env
                                                                  FStar_Reflection_Data.fstar_refl_env in
                                                              let uu____1436
                                                                =
                                                                let uu____1439
                                                                  =
                                                                  mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                let uu____1440
                                                                  =
                                                                  let uu____1443
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                  [uu____1443] in
                                                                uu____1439 ::
                                                                  uu____1440 in
                                                              uu____1435 ::
                                                                uu____1436 in
                                                            uu____1426 ::
                                                              uu____1432 in
                                                          uu____1422 ::
                                                            uu____1423 in
                                                        uu____1418 ::
                                                          uu____1419 in
                                                      uu____1414 ::
                                                        uu____1415 in
                                                    uu____1410 :: uu____1411 in
                                                  uu____1406 :: uu____1407 in
                                                uu____1400 :: uu____1403 in
                                              uu____1396 :: uu____1397 in
                                            uu____1392 :: uu____1393 in
                                          uu____1384 :: uu____1389 in
                                        uu____1380 :: uu____1381 in
                                      uu____1376 :: uu____1377 in
                                    uu____1368 :: uu____1373 in
                                  uu____1364 :: uu____1365 in
                                uu____1336 :: uu____1361 in
                              uu____1332 :: uu____1333 in
                            uu____1328 :: uu____1329 in
                          uu____1324 :: uu____1325 in
                        uu____1320 :: uu____1321 in
                      uu____1316 :: uu____1317 in
                    uu____1312 :: uu____1313 in
                  uu____1308 :: uu____1309 in
                uu____1304 :: uu____1305 in
              uu____1298 :: uu____1301 in
            uu____1285 :: uu____1295 in
          uu____1277 :: uu____1282 in
        uu____1261 :: uu____1274 in
      uu____1257 :: uu____1258 in
    FStar_List.append uu____1254
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0:
  'Ab .
    (FStar_Syntax_Syntax.term -> 'Ab) ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let tm =
             let uu____1456 =
               let uu____1457 =
                 let uu____1458 =
                   let uu____1459 =
                     FStar_Tactics_Embedding.embed_proofstate proof_state in
                   FStar_Syntax_Syntax.as_arg uu____1459 in
                 [uu____1458] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1457 in
             uu____1456 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let steps =
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           let uu____1465 =
             FStar_All.pipe_left FStar_Tactics_Basic.mlog
               (fun uu____1474  ->
                  let uu____1475 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "Starting normalizer with %s\n"
                    uu____1475) in
           FStar_Tactics_Basic.bind uu____1465
             (fun uu____1479  ->
                let result =
                  let uu____1481 = primitive_steps proof_state in
                  FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                    uu____1481 steps
                    proof_state.FStar_Tactics_Basic.main_context tm in
                let uu____1484 =
                  FStar_All.pipe_left FStar_Tactics_Basic.mlog
                    (fun uu____1493  ->
                       let uu____1494 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.print1 "Reduced tactic: got %s\n"
                         uu____1494) in
                FStar_Tactics_Basic.bind uu____1484
                  (fun uu____1500  ->
                     let uu____1501 =
                       FStar_Tactics_Embedding.unembed_result proof_state
                         result unembed_b in
                     match uu____1501 with
                     | FStar_Util.Inl (b,ps) ->
                         let uu____1526 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1526
                           (fun uu____1530  -> FStar_Tactics_Basic.ret b)
                     | FStar_Util.Inr (msg,ps) ->
                         let uu____1541 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1541
                           (fun uu____1545  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ:
  'a .
    'a FStar_Tactics_Basic.tac ->
      FStar_Tactics_Basic.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Tactics_Basic.goal Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2
  =
  fun tau  ->
    fun env  ->
      fun typ  ->
        let uu____1577 = FStar_TypeChecker_Env.clear_expected_typ env in
        match uu____1577 with
        | (env1,uu____1591) ->
            let env2 =
              let uu___114_1597 = env1 in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___114_1597.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___114_1597.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___114_1597.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___114_1597.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___114_1597.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___114_1597.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___114_1597.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___114_1597.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___114_1597.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp = false;
                FStar_TypeChecker_Env.effects =
                  (uu___114_1597.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___114_1597.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs =
                  (uu___114_1597.FStar_TypeChecker_Env.letrecs);
                FStar_TypeChecker_Env.top_level =
                  (uu___114_1597.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___114_1597.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___114_1597.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___114_1597.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___114_1597.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___114_1597.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___114_1597.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.type_of =
                  (uu___114_1597.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___114_1597.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___114_1597.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qname_and_index =
                  (uu___114_1597.FStar_TypeChecker_Env.qname_and_index);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___114_1597.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth =
                  (uu___114_1597.FStar_TypeChecker_Env.synth);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___114_1597.FStar_TypeChecker_Env.is_native_tactic)
              } in
            let uu____1598 =
              FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
            (match uu____1598 with
             | (ps,w) ->
                 let r =
                   try FStar_Tactics_Basic.run tau ps
                   with
                   | FStar_Tactics_Basic.TacFailure s ->
                       FStar_Tactics_Basic.Failed
                         ((Prims.strcat "EXCEPTION: " s), ps) in
                 (match r with
                  | FStar_Tactics_Basic.Success (uu____1632,ps1) ->
                      ((let uu____1635 = FStar_ST.read tacdbg in
                        if uu____1635
                        then
                          let uu____1646 =
                            FStar_Syntax_Print.term_to_string w in
                          FStar_Util.print1 "Tactic generated proofterm %s\n"
                            uu____1646
                        else ());
                       FStar_List.iter
                         (fun g  ->
                            let uu____1653 =
                              FStar_Tactics_Basic.is_irrelevant g in
                            if uu____1653
                            then
                              let uu____1654 =
                                FStar_TypeChecker_Rel.teq_nosmt
                                  g.FStar_Tactics_Basic.context
                                  g.FStar_Tactics_Basic.witness
                                  FStar_Syntax_Util.exp_unit in
                              (if uu____1654
                               then ()
                               else
                                 (let uu____1656 =
                                    let uu____1657 =
                                      FStar_Syntax_Print.term_to_string
                                        g.FStar_Tactics_Basic.witness in
                                    FStar_Util.format1
                                      "Irrelevant tactic witness does not unify with (): %s"
                                      uu____1657 in
                                  failwith uu____1656))
                            else ())
                         (FStar_List.append ps1.FStar_Tactics_Basic.goals
                            ps1.FStar_Tactics_Basic.smt_goals);
                       (let g =
                          let uu___117_1660 =
                            FStar_TypeChecker_Rel.trivial_guard in
                          {
                            FStar_TypeChecker_Env.guard_f =
                              (uu___117_1660.FStar_TypeChecker_Env.guard_f);
                            FStar_TypeChecker_Env.deferred =
                              (uu___117_1660.FStar_TypeChecker_Env.deferred);
                            FStar_TypeChecker_Env.univ_ineqs =
                              (uu___117_1660.FStar_TypeChecker_Env.univ_ineqs);
                            FStar_TypeChecker_Env.implicits =
                              (ps1.FStar_Tactics_Basic.all_implicits)
                          } in
                        let g1 =
                          let uu____1662 =
                            FStar_TypeChecker_Rel.solve_deferred_constraints
                              env2 g in
                          FStar_All.pipe_right uu____1662
                            FStar_TypeChecker_Rel.resolve_implicits_lax in
                        FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                        ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                            ps1.FStar_Tactics_Basic.smt_goals), w)))
                  | FStar_Tactics_Basic.Failed (s,ps1) ->
                      (FStar_Tactics_Basic.dump_proofstate ps1
                         "at the time of failure";
                       (let uu____1669 =
                          let uu____1670 =
                            let uu____1675 =
                              FStar_Util.format1 "user tactic failed: %s" s in
                            (uu____1675, (typ.FStar_Syntax_Syntax.pos)) in
                          FStar_Errors.Error uu____1670 in
                        raise uu____1669))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1686 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1691 -> false
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
        let uu____1720 = FStar_Syntax_Util.head_and_args t in
        match uu____1720 with
        | (hd1,args) ->
            let uu____1763 =
              let uu____1776 =
                let uu____1777 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1777.FStar_Syntax_Syntax.n in
              (uu____1776, args) in
            (match uu____1763 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1796))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1865 =
                     let uu____1872 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     run_tactic_on_typ uu____1872 e assertion in
                   (match uu____1865 with
                    | (gs,uu____1882) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1934 =
                     run_tactic_on_typ FStar_Tactics_Basic.idtac e assertion in
                   (match uu____1934 with
                    | (gs,uu____1948) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | uu____1960 -> (t, []))
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
          let uu____2030 =
            let uu____2037 =
              let uu____2038 = FStar_Syntax_Subst.compress t in
              uu____2038.FStar_Syntax_Syntax.n in
            match uu____2037 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2053 = traverse f pol e t1 in
                (match uu____2053 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____2080 = traverse f pol e t1 in
                (match uu____2080 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2102;
                   FStar_Syntax_Syntax.vars = uu____2103;_},(p,uu____2105)::
                 (q,uu____2107)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
                let uu____2147 = traverse f (flip pol) e p in
                (match uu____2147 with
                 | (p',gs1) ->
                     let uu____2166 =
                       let uu____2173 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____2173 q in
                     (match uu____2166 with
                      | (q',gs2) ->
                          let uu____2186 =
                            let uu____2187 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____2187.FStar_Syntax_Syntax.n in
                          (uu____2186, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____2214 = traverse f pol e hd1 in
                (match uu____2214 with
                 | (hd',gs1) ->
                     let uu____2233 =
                       FStar_List.fold_right
                         (fun uu____2271  ->
                            fun uu____2272  ->
                              match (uu____2271, uu____2272) with
                              | ((a,q),(as',gs)) ->
                                  let uu____2353 = traverse f pol e a in
                                  (match uu____2353 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____2233 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2457 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2457 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2471 =
                       let uu____2486 =
                         FStar_List.map
                           (fun uu____2519  ->
                              match uu____2519 with
                              | (bv,aq) ->
                                  let uu____2536 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2536 with
                                   | (s',gs) ->
                                       (((let uu___118_2566 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___118_2566.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___118_2566.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2486 in
                     (match uu____2471 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2630 = traverse f pol e' topen in
                          (match uu____2630 with
                           | (topen',gs2) ->
                               let uu____2649 =
                                 let uu____2650 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2650.FStar_Syntax_Syntax.n in
                               (uu____2649, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2030 with
          | (tn',gs) ->
              let t' =
                let uu___119_2673 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___119_2673.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_2673.FStar_Syntax_Syntax.vars)
                } in
              let uu____2674 = f pol e t' in
              (match uu____2674 with
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
      FStar_Syntax_Util.un_squash tn
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____2733 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____2733);
      (let uu____2745 = FStar_ST.read tacdbg in
       if uu____2745
       then
         let uu____2756 =
           let uu____2757 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2757
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2758 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2756
           uu____2758
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2787 = traverse by_tactic_interp Pos env goal in
       match uu____2787 with
       | (t',gs) ->
           ((let uu____2809 = FStar_ST.read tacdbg in
             if uu____2809
             then
               let uu____2820 =
                 let uu____2821 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2821
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2822 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2820 uu____2822
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2869  ->
                    fun g  ->
                      match uu____2869 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2914 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty in
                            match uu____2914 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2917 =
                                  let uu____2918 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2918 in
                                failwith uu____2917
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____2921 = FStar_ST.read tacdbg in
                            if uu____2921
                            then
                              let uu____2932 = FStar_Util.string_of_int n1 in
                              let uu____2933 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2932 uu____2933
                            else ());
                           (let gt' =
                              let uu____2936 =
                                let uu____2937 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____2937 in
                              FStar_TypeChecker_Util.label uu____2936
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt',
                                 (g.FStar_Tactics_Basic.opts)) :: gs1))))) s
                 gs in
             let uu____2952 = s1 in
             match uu____2952 with
             | (uu____2973,gs1) ->
                 let uu____2991 =
                   let uu____2998 = FStar_Options.peek () in
                   (env, t', uu____2998) in
                 uu____2991 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____3010 =
        let uu____3011 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____3011 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3010 [FStar_Syntax_Syntax.U_zero] in
    let uu____3012 =
      let uu____3013 =
        let uu____3014 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____3015 =
          let uu____3018 = FStar_Syntax_Syntax.as_arg a in [uu____3018] in
        uu____3014 :: uu____3015 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3013 in
    uu____3012 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____3034 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.write tacdbg uu____3034);
        (let uu____3045 =
           let uu____3052 =
             let uu____3055 = reify_tactic tau in
             unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____3055 in
           run_tactic_on_typ uu____3052 env typ in
         match uu____3045 with
         | (gs,w) ->
             (match gs with
              | [] -> w
              | uu____3062::uu____3063 ->
                  raise
                    (FStar_Errors.Error
                       ("synthesis left open goals",
                         (typ.FStar_Syntax_Syntax.pos)))))