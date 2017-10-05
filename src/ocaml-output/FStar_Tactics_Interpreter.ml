open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let mk_tactic_interpretation_0:
  'a .
    FStar_Tactics_Types.proofstate ->
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
              | (embedded_state,uu____61)::[] ->
                  (FStar_Tactics_Basic.log ps
                     (fun uu____82  ->
                        let uu____83 = FStar_Ident.string_of_lid nm in
                        let uu____84 = FStar_Syntax_Print.args_to_string args in
                        FStar_Util.print2 "Reached %s, args are: %s\n"
                          uu____83 uu____84);
                   (let ps1 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    let res = FStar_Tactics_Basic.run t ps1 in
                    let uu____89 =
                      FStar_Tactics_Embedding.embed_result ps1 res embed_a
                        t_a in
                    FStar_Pervasives_Native.Some uu____89))
              | uu____90 ->
                  failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1:
  'a 'b .
    FStar_Tactics_Types.proofstate ->
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
                | (b,uu____163)::(embedded_state,uu____165)::[] ->
                    (FStar_Tactics_Basic.log ps
                       (fun uu____196  ->
                          let uu____197 = FStar_Ident.string_of_lid nm in
                          let uu____198 =
                            FStar_Syntax_Print.term_to_string embedded_state in
                          FStar_Util.print2 "Reached %s, goals are: %s\n"
                            uu____197 uu____198);
                     (let ps1 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      let res =
                        let uu____203 =
                          let uu____206 = unembed_b b in t uu____206 in
                        FStar_Tactics_Basic.run uu____203 ps1 in
                      let uu____207 =
                        FStar_Tactics_Embedding.embed_result ps1 res embed_a
                          t_a in
                      FStar_Pervasives_Native.Some uu____207))
                | uu____208 ->
                    let uu____209 =
                      let uu____210 = FStar_Ident.string_of_lid nm in
                      let uu____211 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____210 uu____211 in
                    failwith uu____209
let mk_tactic_interpretation_2:
  'a 'b 'c .
    FStar_Tactics_Types.proofstate ->
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
                  | (a,uu____303)::(b,uu____305)::(embedded_state,uu____307)::[]
                      ->
                      (FStar_Tactics_Basic.log ps
                         (fun uu____348  ->
                            let uu____349 = FStar_Ident.string_of_lid nm in
                            let uu____350 =
                              FStar_Syntax_Print.term_to_string
                                embedded_state in
                            FStar_Util.print2 "Reached %s, goals are: %s\n"
                              uu____349 uu____350);
                       (let ps1 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        let res =
                          let uu____355 =
                            let uu____358 = unembed_a a in
                            let uu____359 = unembed_b b in
                            t uu____358 uu____359 in
                          FStar_Tactics_Basic.run uu____355 ps1 in
                        let uu____360 =
                          FStar_Tactics_Embedding.embed_result ps1 res
                            embed_c t_c in
                        FStar_Pervasives_Native.Some uu____360))
                  | uu____361 ->
                      let uu____362 =
                        let uu____363 = FStar_Ident.string_of_lid nm in
                        let uu____364 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____363 uu____364 in
                      failwith uu____362
let mk_tactic_interpretation_3:
  'a 'b 'c 'd .
    FStar_Tactics_Types.proofstate ->
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
                    | (a,uu____475)::(b,uu____477)::(c,uu____479)::(embedded_state,uu____481)::[]
                        ->
                        (FStar_Tactics_Basic.log ps
                           (fun uu____532  ->
                              let uu____533 = FStar_Ident.string_of_lid nm in
                              let uu____534 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____533 uu____534);
                         (let ps1 =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state in
                          let res =
                            let uu____539 =
                              let uu____542 = unembed_a a in
                              let uu____543 = unembed_b b in
                              let uu____544 = unembed_c c in
                              t uu____542 uu____543 uu____544 in
                            FStar_Tactics_Basic.run uu____539 ps1 in
                          let uu____545 =
                            FStar_Tactics_Embedding.embed_result ps1 res
                              embed_d t_d in
                          FStar_Pervasives_Native.Some uu____545))
                    | uu____546 ->
                        let uu____547 =
                          let uu____548 = FStar_Ident.string_of_lid nm in
                          let uu____549 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____548 uu____549 in
                        failwith uu____547
let mk_tactic_interpretation_5:
  'a 'b 'c 'd 'e 'f .
    FStar_Tactics_Types.proofstate ->
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
                        | (a,uu____698)::(b,uu____700)::(c,uu____702)::
                            (d,uu____704)::(e,uu____706)::(embedded_state,uu____708)::[]
                            ->
                            (FStar_Tactics_Basic.log ps
                               (fun uu____779  ->
                                  let uu____780 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____781 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____780
                                    uu____781);
                             (let ps1 =
                                FStar_Tactics_Embedding.unembed_proofstate
                                  embedded_state in
                              let res =
                                let uu____786 =
                                  let uu____789 = unembed_a a in
                                  let uu____790 = unembed_b b in
                                  let uu____791 = unembed_c c in
                                  let uu____792 = unembed_d d in
                                  let uu____793 = unembed_e e in
                                  t uu____789 uu____790 uu____791 uu____792
                                    uu____793 in
                                FStar_Tactics_Basic.run uu____786 ps1 in
                              let uu____794 =
                                FStar_Tactics_Embedding.embed_result ps1 res
                                  embed_f t_f in
                              FStar_Pervasives_Native.Some uu____794))
                        | uu____795 ->
                            let uu____796 =
                              let uu____797 = FStar_Ident.string_of_lid nm in
                              let uu____798 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____797 uu____798 in
                            failwith uu____796
let step_from_native_step:
  FStar_Tactics_Types.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      {
        FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Normalize.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> s.FStar_Tactics_Native.tactic ps args)
      }
let rec primitive_steps:
  FStar_Tactics_Types.proofstate ->
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
    let decr_depth_interp rng args =
      match args with
      | (ps1,uu____1229)::[] ->
          let uu____1246 =
            let uu____1247 =
              let uu____1248 = FStar_Tactics_Embedding.unembed_proofstate ps1 in
              FStar_Tactics_Types.decr_depth uu____1248 in
            FStar_Tactics_Embedding.embed_proofstate uu____1247 in
          FStar_Pervasives_Native.Some uu____1246
      | uu____1249 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1253 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1253;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp rng args =
      match args with
      | (ps1,uu____1266)::[] ->
          let uu____1283 =
            let uu____1284 =
              let uu____1285 = FStar_Tactics_Embedding.unembed_proofstate ps1 in
              FStar_Tactics_Types.incr_depth uu____1285 in
            FStar_Tactics_Embedding.embed_proofstate uu____1284 in
          FStar_Pervasives_Native.Some uu____1283
      | uu____1286 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1290 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1290;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp rng args =
      match args with
      | (ps1,uu____1307)::[] ->
          ((let uu____1325 = FStar_Tactics_Embedding.unembed_proofstate ps1 in
            FStar_Tactics_Types.tracepoint uu____1325);
           FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1328 -> failwith "Unexpected application of tracepoint" in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let uu____1335 =
      let uu____1338 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
      let uu____1339 =
        let uu____1342 =
          mktac2 "__trytac" (fun uu____1348  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Syntax_Embeddings.embed_option (fun t  -> t)
               FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit in
        let uu____1355 =
          let uu____1358 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1359 =
            let uu____1362 =
              let uu____1363 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Syntax_Embeddings.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1363 in
            let uu____1368 =
              let uu____1371 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Syntax_Embeddings.unembed_list
                     FStar_Syntax_Embeddings.unembed_norm_step)
                  FStar_Syntax_Embeddings.embed_unit
                  FStar_Syntax_Syntax.t_unit in
              let uu____1374 =
                let uu____1377 =
                  mktac2 "__norm_term" FStar_Tactics_Basic.norm_term
                    (FStar_Syntax_Embeddings.unembed_list
                       FStar_Syntax_Embeddings.unembed_norm_step)
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_term
                    FStar_Reflection_Data.fstar_refl_term in
                let uu____1380 =
                  let uu____1383 =
                    mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Syntax_Embeddings.unembed_string
                      FStar_Syntax_Embeddings.embed_unit
                      FStar_Syntax_Syntax.t_unit in
                  let uu____1384 =
                    let uu____1387 =
                      mktac1 "__binder_retype"
                        FStar_Tactics_Basic.binder_retype
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1388 =
                      let uu____1391 =
                        mktac0 "__revert" FStar_Tactics_Basic.revert
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____1392 =
                        let uu____1395 =
                          mktac0 "__clear_top" FStar_Tactics_Basic.clear_top
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____1396 =
                          let uu____1399 =
                            mktac1 "__clear" FStar_Tactics_Basic.clear
                              FStar_Reflection_Basic.unembed_binder
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____1400 =
                            let uu____1403 =
                              mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                                FStar_Reflection_Basic.unembed_binder
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____1404 =
                              let uu____1407 =
                                mktac0 "__smt" FStar_Tactics_Basic.smt
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____1408 =
                                let uu____1411 =
                                  mktac1 "__exact" FStar_Tactics_Basic.exact
                                    FStar_Reflection_Basic.unembed_term
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____1412 =
                                  let uu____1415 =
                                    mktac1 "__exact_lemma"
                                      FStar_Tactics_Basic.exact_lemma
                                      FStar_Reflection_Basic.unembed_term
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____1416 =
                                    let uu____1419 =
                                      mktac1 "__apply"
                                        (FStar_Tactics_Basic.apply true)
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____1420 =
                                      let uu____1423 =
                                        mktac1 "__apply_raw"
                                          (FStar_Tactics_Basic.apply false)
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____1424 =
                                        let uu____1427 =
                                          mktac1 "__apply_lemma"
                                            FStar_Tactics_Basic.apply_lemma
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____1428 =
                                          let uu____1431 =
                                            mktac5 "__divide"
                                              (fun uu____1442  ->
                                                 fun uu____1443  ->
                                                   FStar_Tactics_Basic.divide)
                                              (fun t  -> t) (fun t  -> t)
                                              FStar_Syntax_Embeddings.unembed_int
                                              (unembed_tactic_0 (fun t  -> t))
                                              (unembed_tactic_0 (fun t  -> t))
                                              (FStar_Syntax_Embeddings.embed_pair
                                                 (fun t  -> t)
                                                 FStar_Syntax_Syntax.t_unit
                                                 (fun t  -> t)
                                                 FStar_Syntax_Syntax.t_unit)
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____1456 =
                                            let uu____1459 =
                                              mktac1 "__set_options"
                                                FStar_Tactics_Basic.set_options
                                                FStar_Syntax_Embeddings.unembed_string
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____1460 =
                                              let uu____1463 =
                                                mktac2 "__seq"
                                                  FStar_Tactics_Basic.seq
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  FStar_Syntax_Embeddings.embed_unit
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____1468 =
                                                let uu____1471 =
                                                  mktac2 "__unquote"
                                                    FStar_Tactics_Basic.unquote
                                                    (fun t  -> t)
                                                    FStar_Reflection_Basic.unembed_term
                                                    (fun t  -> t)
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____1476 =
                                                  let uu____1479 =
                                                    mktac1 "__prune"
                                                      FStar_Tactics_Basic.prune
                                                      FStar_Syntax_Embeddings.unembed_string
                                                      FStar_Syntax_Embeddings.embed_unit
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____1480 =
                                                    let uu____1483 =
                                                      mktac1 "__addns"
                                                        FStar_Tactics_Basic.addns
                                                        FStar_Syntax_Embeddings.unembed_string
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____1484 =
                                                      let uu____1487 =
                                                        mktac1 "__print"
                                                          (fun x  ->
                                                             FStar_Tactics_Basic.tacprint
                                                               x;
                                                             FStar_Tactics_Basic.ret
                                                               ())
                                                          FStar_Syntax_Embeddings.unembed_string
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____1492 =
                                                        let uu____1495 =
                                                          mktac1 "__dump"
                                                            FStar_Tactics_Basic.print_proof_state
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____1496 =
                                                          let uu____1499 =
                                                            mktac1 "__dump1"
                                                              FStar_Tactics_Basic.print_proof_state1
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____1500 =
                                                            let uu____1503 =
                                                              mktac1
                                                                "__pointwise"
                                                                FStar_Tactics_Basic.pointwise
                                                                (unembed_tactic_0
                                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____1506 =
                                                              let uu____1509
                                                                =
                                                                mktac0
                                                                  "__trefl"
                                                                  FStar_Tactics_Basic.trefl
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____1510
                                                                =
                                                                let uu____1513
                                                                  =
                                                                  mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____1514
                                                                  =
                                                                  let uu____1517
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____1518
                                                                    =
                                                                    let uu____1521
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1522
                                                                    =
                                                                    let uu____1525
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1526
                                                                    =
                                                                    let uu____1529
                                                                    =
                                                                    let uu____1530
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Reflection_Data.fstar_refl_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    (FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term)
                                                                    uu____1530 in
                                                                    let uu____1535
                                                                    =
                                                                    let uu____1538
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1539
                                                                    =
                                                                    let uu____1542
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1543
                                                                    =
                                                                    let uu____1546
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1547
                                                                    =
                                                                    let uu____1550
                                                                    =
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    (FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1553
                                                                    =
                                                                    let uu____1556
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____1557
                                                                    =
                                                                    let uu____1560
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____1560;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step] in
                                                                    uu____1556
                                                                    ::
                                                                    uu____1557 in
                                                                    uu____1550
                                                                    ::
                                                                    uu____1553 in
                                                                    uu____1546
                                                                    ::
                                                                    uu____1547 in
                                                                    uu____1542
                                                                    ::
                                                                    uu____1543 in
                                                                    uu____1538
                                                                    ::
                                                                    uu____1539 in
                                                                    uu____1529
                                                                    ::
                                                                    uu____1535 in
                                                                    uu____1525
                                                                    ::
                                                                    uu____1526 in
                                                                    uu____1521
                                                                    ::
                                                                    uu____1522 in
                                                                  uu____1517
                                                                    ::
                                                                    uu____1518 in
                                                                uu____1513 ::
                                                                  uu____1514 in
                                                              uu____1509 ::
                                                                uu____1510 in
                                                            uu____1503 ::
                                                              uu____1506 in
                                                          uu____1499 ::
                                                            uu____1500 in
                                                        uu____1495 ::
                                                          uu____1496 in
                                                      uu____1487 ::
                                                        uu____1492 in
                                                    uu____1483 :: uu____1484 in
                                                  uu____1479 :: uu____1480 in
                                                uu____1471 :: uu____1476 in
                                              uu____1463 :: uu____1468 in
                                            uu____1459 :: uu____1460 in
                                          uu____1431 :: uu____1456 in
                                        uu____1427 :: uu____1428 in
                                      uu____1423 :: uu____1424 in
                                    uu____1419 :: uu____1420 in
                                  uu____1415 :: uu____1416 in
                                uu____1411 :: uu____1412 in
                              uu____1407 :: uu____1408 in
                            uu____1403 :: uu____1404 in
                          uu____1399 :: uu____1400 in
                        uu____1395 :: uu____1396 in
                      uu____1391 :: uu____1392 in
                    uu____1387 :: uu____1388 in
                  uu____1383 :: uu____1384 in
                uu____1377 :: uu____1380 in
              uu____1371 :: uu____1374 in
            uu____1362 :: uu____1368 in
          uu____1358 :: uu____1359 in
        uu____1342 :: uu____1355 in
      uu____1338 :: uu____1339 in
    FStar_List.append uu____1335
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
             let uu____1573 =
               let uu____1574 =
                 let uu____1575 =
                   let uu____1576 =
                     FStar_Tactics_Embedding.embed_proofstate proof_state in
                   FStar_Syntax_Syntax.as_arg uu____1576 in
                 [uu____1575] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1574 in
             uu____1573 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let steps =
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           let uu____1582 =
             FStar_All.pipe_left FStar_Tactics_Basic.mlog
               (fun uu____1591  ->
                  let uu____1592 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "Starting normalizer with %s\n"
                    uu____1592) in
           FStar_Tactics_Basic.bind uu____1582
             (fun uu____1596  ->
                let result =
                  let uu____1598 = primitive_steps proof_state in
                  FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                    uu____1598 steps
                    proof_state.FStar_Tactics_Types.main_context tm in
                let uu____1601 =
                  FStar_All.pipe_left FStar_Tactics_Basic.mlog
                    (fun uu____1610  ->
                       let uu____1611 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.print1 "Reduced tactic: got %s\n"
                         uu____1611) in
                FStar_Tactics_Basic.bind uu____1601
                  (fun uu____1617  ->
                     let uu____1618 =
                       FStar_Tactics_Embedding.unembed_result proof_state
                         result unembed_b in
                     match uu____1618 with
                     | FStar_Util.Inl (b,ps) ->
                         let uu____1643 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1643
                           (fun uu____1647  -> FStar_Tactics_Basic.ret b)
                     | FStar_Util.Inr (msg,ps) ->
                         let uu____1658 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1658
                           (fun uu____1662  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Basic.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Tactics_Types.goal Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun tactic  ->
    fun env  ->
      fun typ  ->
        (let uu____1688 = FStar_ST.op_Bang tacdbg in
         if uu____1688
         then
           let uu____1735 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____1735
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         (let uu____1739 = FStar_ST.op_Bang tacdbg in
          if uu____1739
          then
            let uu____1786 = FStar_Syntax_Print.term_to_string tactic1 in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____1786
          else ());
         (let uu____1788 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1 in
          match uu____1788 with
          | (tactic2,uu____1802,uu____1803) ->
              let tau =
                unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic2 in
              let uu____1807 = FStar_TypeChecker_Env.clear_expected_typ env in
              (match uu____1807 with
               | (env1,uu____1821) ->
                   let env2 =
                     let uu___154_1827 = env1 in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___154_1827.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___154_1827.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___154_1827.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___154_1827.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___154_1827.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___154_1827.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___154_1827.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___154_1827.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___154_1827.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp = false;
                       FStar_TypeChecker_Env.effects =
                         (uu___154_1827.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___154_1827.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___154_1827.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___154_1827.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___154_1827.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___154_1827.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___154_1827.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___154_1827.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___154_1827.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___154_1827.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___154_1827.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___154_1827.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___154_1827.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___154_1827.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___154_1827.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___154_1827.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___154_1827.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___154_1827.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___154_1827.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___154_1827.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___154_1827.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___154_1827.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___154_1827.FStar_TypeChecker_Env.dsenv)
                     } in
                   let uu____1828 =
                     FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
                   (match uu____1828 with
                    | (ps,w) ->
                        let uu____1841 = FStar_Tactics_Basic.run tau ps in
                        (match uu____1841 with
                         | FStar_Tactics_Result.Success (uu____1850,ps1) ->
                             ((let uu____1853 = FStar_ST.op_Bang tacdbg in
                               if uu____1853
                               then
                                 let uu____1900 =
                                   FStar_Syntax_Print.term_to_string w in
                                 FStar_Util.print1
                                   "Tactic generated proofterm %s\n"
                                   uu____1900
                               else ());
                              FStar_List.iter
                                (fun g  ->
                                   let uu____1907 =
                                     FStar_Tactics_Basic.is_irrelevant g in
                                   if uu____1907
                                   then
                                     let uu____1908 =
                                       FStar_TypeChecker_Rel.teq_nosmt
                                         g.FStar_Tactics_Types.context
                                         g.FStar_Tactics_Types.witness
                                         FStar_Syntax_Util.exp_unit in
                                     (if uu____1908
                                      then ()
                                      else
                                        (let uu____1910 =
                                           let uu____1911 =
                                             FStar_Syntax_Print.term_to_string
                                               g.FStar_Tactics_Types.witness in
                                           FStar_Util.format1
                                             "Irrelevant tactic witness does not unify with (): %s"
                                             uu____1911 in
                                         failwith uu____1910))
                                   else ())
                                (FStar_List.append
                                   ps1.FStar_Tactics_Types.goals
                                   ps1.FStar_Tactics_Types.smt_goals);
                              (let g =
                                 let uu___155_1914 =
                                   FStar_TypeChecker_Rel.trivial_guard in
                                 {
                                   FStar_TypeChecker_Env.guard_f =
                                     (uu___155_1914.FStar_TypeChecker_Env.guard_f);
                                   FStar_TypeChecker_Env.deferred =
                                     (uu___155_1914.FStar_TypeChecker_Env.deferred);
                                   FStar_TypeChecker_Env.univ_ineqs =
                                     (uu___155_1914.FStar_TypeChecker_Env.univ_ineqs);
                                   FStar_TypeChecker_Env.implicits =
                                     (ps1.FStar_Tactics_Types.all_implicits)
                                 } in
                               let g1 =
                                 let uu____1916 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env2 g in
                                 FStar_All.pipe_right uu____1916
                                   FStar_TypeChecker_Rel.resolve_implicits_tac in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 g1;
                               ((FStar_List.append
                                   ps1.FStar_Tactics_Types.goals
                                   ps1.FStar_Tactics_Types.smt_goals), w)))
                         | FStar_Tactics_Result.Failed (s,ps1) ->
                             (FStar_Tactics_Basic.dump_proofstate ps1
                                "at the time of failure";
                              (let uu____1923 =
                                 let uu____1924 =
                                   let uu____1929 =
                                     FStar_Util.format1
                                       "user tactic failed: %s" s in
                                   (uu____1929,
                                     (typ.FStar_Syntax_Syntax.pos)) in
                                 FStar_Errors.Error uu____1924 in
                               FStar_Exn.raise uu____1923)))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1940 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1945 -> false
let flip: pol -> pol = fun p  -> match p with | Pos  -> Neg | Neg  -> Pos
let by_tactic_interp:
  pol ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Tactics_Types.goal Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1974 = FStar_Syntax_Util.head_and_args t in
        match uu____1974 with
        | (hd1,args) ->
            let uu____2017 =
              let uu____2030 =
                let uu____2031 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2031.FStar_Syntax_Syntax.n in
              (uu____2030, args) in
            (match uu____2017 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2050))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2119 = run_tactic_on_typ tactic e assertion in
                   (match uu____2119 with
                    | (gs,uu____2133) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2185 =
                     let uu____2188 =
                       let uu____2189 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____2189 in
                     [uu____2188] in
                   (FStar_Syntax_Util.t_true, uu____2185)
                 else (assertion, [])
             | uu____2205 -> (t, []))
let rec traverse:
  (pol ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term,FStar_Tactics_Types.goal Prims.list)
           FStar_Pervasives_Native.tuple2)
    ->
    pol ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Tactics_Types.goal Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let uu____2275 =
            let uu____2282 =
              let uu____2283 = FStar_Syntax_Subst.compress t in
              uu____2283.FStar_Syntax_Syntax.n in
            match uu____2282 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2298 = traverse f pol e t1 in
                (match uu____2298 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____2325 = traverse f pol e t1 in
                (match uu____2325 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2347;
                   FStar_Syntax_Syntax.vars = uu____2348;_},(p,uu____2350)::
                 (q,uu____2352)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2392 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2392 in
                let uu____2393 = traverse f (flip pol) e p in
                (match uu____2393 with
                 | (p',gs1) ->
                     let uu____2412 =
                       let uu____2419 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____2419 q in
                     (match uu____2412 with
                      | (q',gs2) ->
                          let uu____2432 =
                            let uu____2433 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____2433.FStar_Syntax_Syntax.n in
                          (uu____2432, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____2460 = traverse f pol e hd1 in
                (match uu____2460 with
                 | (hd',gs1) ->
                     let uu____2479 =
                       FStar_List.fold_right
                         (fun uu____2517  ->
                            fun uu____2518  ->
                              match (uu____2517, uu____2518) with
                              | ((a,q),(as',gs)) ->
                                  let uu____2599 = traverse f pol e a in
                                  (match uu____2599 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____2479 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2703 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2703 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2717 =
                       let uu____2732 =
                         FStar_List.map
                           (fun uu____2765  ->
                              match uu____2765 with
                              | (bv,aq) ->
                                  let uu____2782 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2782 with
                                   | (s',gs) ->
                                       (((let uu___156_2812 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___156_2812.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___156_2812.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2732 in
                     (match uu____2717 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2876 = traverse f pol e' topen in
                          (match uu____2876 with
                           | (topen',gs2) ->
                               let uu____2895 =
                                 let uu____2896 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2896.FStar_Syntax_Syntax.n in
                               (uu____2895, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2275 with
          | (tn',gs) ->
              let t' =
                let uu___157_2919 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___157_2919.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___157_2919.FStar_Syntax_Syntax.vars)
                } in
              let uu____2920 = f pol e t' in
              (match uu____2920 with
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
      (let uu____2979 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____2979);
      (let uu____3027 = FStar_ST.op_Bang tacdbg in
       if uu____3027
       then
         let uu____3074 =
           let uu____3075 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____3075
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____3076 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3074
           uu____3076
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____3105 = traverse by_tactic_interp Pos env goal in
       match uu____3105 with
       | (t',gs) ->
           ((let uu____3127 = FStar_ST.op_Bang tacdbg in
             if uu____3127
             then
               let uu____3174 =
                 let uu____3175 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____3175
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____3176 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3174 uu____3176
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3223  ->
                    fun g  ->
                      match uu____3223 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3268 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____3268 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3271 =
                                  let uu____3272 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____3272 in
                                failwith uu____3271
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____3275 = FStar_ST.op_Bang tacdbg in
                            if uu____3275
                            then
                              let uu____3322 = FStar_Util.string_of_int n1 in
                              let uu____3323 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3322 uu____3323
                            else ());
                           (let gt' =
                              let uu____3326 =
                                let uu____3327 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____3327 in
                              FStar_TypeChecker_Util.label uu____3326
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____3342 = s1 in
             match uu____3342 with
             | (uu____3363,gs1) ->
                 let uu____3381 =
                   let uu____3388 = FStar_Options.peek () in
                   (env, t', uu____3388) in
                 uu____3381 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____3400 =
        let uu____3401 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____3401 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3400 [FStar_Syntax_Syntax.U_zero] in
    let uu____3402 =
      let uu____3403 =
        let uu____3404 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____3405 =
          let uu____3408 = FStar_Syntax_Syntax.as_arg a in [uu____3408] in
        uu____3404 :: uu____3405 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3403 in
    uu____3402 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____3424 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____3424);
        (let uu____3471 =
           let uu____3478 = reify_tactic tau in
           run_tactic_on_typ uu____3478 env typ in
         match uu____3471 with
         | (gs,w) ->
             let uu____3485 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____3489 =
                      let uu____3490 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____3490 in
                    Prims.op_Negation uu____3489) gs in
             if uu____3485
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)