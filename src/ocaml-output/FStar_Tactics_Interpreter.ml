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
                      FStar_Tactics_Embedding.unembed_proofstate ps
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
                        FStar_Tactics_Embedding.unembed_proofstate ps
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
                          FStar_Tactics_Embedding.unembed_proofstate ps
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
                            FStar_Tactics_Embedding.unembed_proofstate ps
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
                                FStar_Tactics_Embedding.unembed_proofstate ps
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
    let uu____1217 =
      let uu____1220 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
      let uu____1221 =
        let uu____1224 =
          mktac2 "__trytac" (fun uu____1230  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Syntax_Embeddings.embed_option (fun t  -> t)
               FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit in
        let uu____1237 =
          let uu____1240 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1241 =
            let uu____1244 =
              let uu____1245 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Syntax_Embeddings.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1245 in
            let uu____1250 =
              let uu____1253 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Syntax_Embeddings.unembed_list
                     FStar_Syntax_Embeddings.unembed_norm_step)
                  FStar_Syntax_Embeddings.embed_unit
                  FStar_Syntax_Syntax.t_unit in
              let uu____1256 =
                let uu____1259 =
                  mktac2 "__norm_term" FStar_Tactics_Basic.norm_term
                    (FStar_Syntax_Embeddings.unembed_list
                       FStar_Syntax_Embeddings.unembed_norm_step)
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_term
                    FStar_Reflection_Data.fstar_refl_term in
                let uu____1262 =
                  let uu____1265 =
                    mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Syntax_Embeddings.unembed_string
                      FStar_Syntax_Embeddings.embed_unit
                      FStar_Syntax_Syntax.t_unit in
                  let uu____1266 =
                    let uu____1269 =
                      mktac1 "__binder_retype"
                        FStar_Tactics_Basic.binder_retype
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1270 =
                      let uu____1273 =
                        mktac0 "__revert" FStar_Tactics_Basic.revert
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____1274 =
                        let uu____1277 =
                          mktac0 "__clear_top" FStar_Tactics_Basic.clear_top
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____1278 =
                          let uu____1281 =
                            mktac1 "__clear" FStar_Tactics_Basic.clear
                              FStar_Reflection_Basic.unembed_binder
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____1282 =
                            let uu____1285 =
                              mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                                FStar_Reflection_Basic.unembed_binder
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____1286 =
                              let uu____1289 =
                                mktac0 "__smt" FStar_Tactics_Basic.smt
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____1290 =
                                let uu____1293 =
                                  mktac1 "__exact" FStar_Tactics_Basic.exact
                                    FStar_Reflection_Basic.unembed_term
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____1294 =
                                  let uu____1297 =
                                    mktac1 "__exact_lemma"
                                      FStar_Tactics_Basic.exact_lemma
                                      FStar_Reflection_Basic.unembed_term
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____1298 =
                                    let uu____1301 =
                                      mktac1 "__apply"
                                        (FStar_Tactics_Basic.apply true)
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____1302 =
                                      let uu____1305 =
                                        mktac1 "__apply_raw"
                                          (FStar_Tactics_Basic.apply false)
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____1306 =
                                        let uu____1309 =
                                          mktac1 "__apply_lemma"
                                            FStar_Tactics_Basic.apply_lemma
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____1310 =
                                          let uu____1313 =
                                            mktac5 "__divide"
                                              (fun uu____1324  ->
                                                 fun uu____1325  ->
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
                                          let uu____1338 =
                                            let uu____1341 =
                                              mktac1 "__set_options"
                                                FStar_Tactics_Basic.set_options
                                                FStar_Syntax_Embeddings.unembed_string
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____1342 =
                                              let uu____1345 =
                                                mktac2 "__seq"
                                                  FStar_Tactics_Basic.seq
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  FStar_Syntax_Embeddings.embed_unit
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____1350 =
                                                let uu____1353 =
                                                  mktac2 "__unquote"
                                                    FStar_Tactics_Basic.unquote
                                                    (fun t  -> t)
                                                    FStar_Reflection_Basic.unembed_term
                                                    (fun t  -> t)
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____1358 =
                                                  let uu____1361 =
                                                    mktac1 "__prune"
                                                      FStar_Tactics_Basic.prune
                                                      FStar_Syntax_Embeddings.unembed_string
                                                      FStar_Syntax_Embeddings.embed_unit
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____1362 =
                                                    let uu____1365 =
                                                      mktac1 "__addns"
                                                        FStar_Tactics_Basic.addns
                                                        FStar_Syntax_Embeddings.unembed_string
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____1366 =
                                                      let uu____1369 =
                                                        mktac1 "__print"
                                                          (fun x  ->
                                                             FStar_Tactics_Basic.tacprint
                                                               x;
                                                             FStar_Tactics_Basic.ret
                                                               ())
                                                          FStar_Syntax_Embeddings.unembed_string
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____1374 =
                                                        let uu____1377 =
                                                          mktac1 "__dump"
                                                            FStar_Tactics_Basic.print_proof_state
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____1378 =
                                                          let uu____1381 =
                                                            mktac1 "__dump1"
                                                              FStar_Tactics_Basic.print_proof_state1
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____1382 =
                                                            let uu____1385 =
                                                              mktac1
                                                                "__pointwise"
                                                                FStar_Tactics_Basic.pointwise
                                                                (unembed_tactic_0
                                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____1388 =
                                                              let uu____1391
                                                                =
                                                                mktac0
                                                                  "__trefl"
                                                                  FStar_Tactics_Basic.trefl
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____1392
                                                                =
                                                                let uu____1395
                                                                  =
                                                                  mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____1396
                                                                  =
                                                                  let uu____1399
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____1400
                                                                    =
                                                                    let uu____1403
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1404
                                                                    =
                                                                    let uu____1407
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1408
                                                                    =
                                                                    let uu____1411
                                                                    =
                                                                    let uu____1412
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
                                                                    uu____1412 in
                                                                    let uu____1417
                                                                    =
                                                                    let uu____1420
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1421
                                                                    =
                                                                    let uu____1424
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1425
                                                                    =
                                                                    let uu____1428
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1429
                                                                    =
                                                                    let uu____1432
                                                                    =
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    (FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1435
                                                                    =
                                                                    let uu____1438
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____1439
                                                                    =
                                                                    let uu____1442
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____1442] in
                                                                    uu____1438
                                                                    ::
                                                                    uu____1439 in
                                                                    uu____1432
                                                                    ::
                                                                    uu____1435 in
                                                                    uu____1428
                                                                    ::
                                                                    uu____1429 in
                                                                    uu____1424
                                                                    ::
                                                                    uu____1425 in
                                                                    uu____1420
                                                                    ::
                                                                    uu____1421 in
                                                                    uu____1411
                                                                    ::
                                                                    uu____1417 in
                                                                    uu____1407
                                                                    ::
                                                                    uu____1408 in
                                                                    uu____1403
                                                                    ::
                                                                    uu____1404 in
                                                                  uu____1399
                                                                    ::
                                                                    uu____1400 in
                                                                uu____1395 ::
                                                                  uu____1396 in
                                                              uu____1391 ::
                                                                uu____1392 in
                                                            uu____1385 ::
                                                              uu____1388 in
                                                          uu____1381 ::
                                                            uu____1382 in
                                                        uu____1377 ::
                                                          uu____1378 in
                                                      uu____1369 ::
                                                        uu____1374 in
                                                    uu____1365 :: uu____1366 in
                                                  uu____1361 :: uu____1362 in
                                                uu____1353 :: uu____1358 in
                                              uu____1345 :: uu____1350 in
                                            uu____1341 :: uu____1342 in
                                          uu____1313 :: uu____1338 in
                                        uu____1309 :: uu____1310 in
                                      uu____1305 :: uu____1306 in
                                    uu____1301 :: uu____1302 in
                                  uu____1297 :: uu____1298 in
                                uu____1293 :: uu____1294 in
                              uu____1289 :: uu____1290 in
                            uu____1285 :: uu____1286 in
                          uu____1281 :: uu____1282 in
                        uu____1277 :: uu____1278 in
                      uu____1273 :: uu____1274 in
                    uu____1269 :: uu____1270 in
                  uu____1265 :: uu____1266 in
                uu____1259 :: uu____1262 in
              uu____1253 :: uu____1256 in
            uu____1244 :: uu____1250 in
          uu____1240 :: uu____1241 in
        uu____1224 :: uu____1237 in
      uu____1220 :: uu____1221 in
    FStar_List.append uu____1217
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
             let uu____1455 =
               let uu____1456 =
                 let uu____1457 =
                   let uu____1458 =
                     FStar_Tactics_Embedding.embed_proofstate proof_state in
                   FStar_Syntax_Syntax.as_arg uu____1458 in
                 [uu____1457] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1456 in
             uu____1455 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let steps =
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           let uu____1464 =
             FStar_All.pipe_left FStar_Tactics_Basic.mlog
               (fun uu____1473  ->
                  let uu____1474 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "Starting normalizer with %s\n"
                    uu____1474) in
           FStar_Tactics_Basic.bind uu____1464
             (fun uu____1478  ->
                let result =
                  let uu____1480 = primitive_steps proof_state in
                  FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                    uu____1480 steps
                    proof_state.FStar_Tactics_Types.main_context tm in
                let uu____1483 =
                  FStar_All.pipe_left FStar_Tactics_Basic.mlog
                    (fun uu____1492  ->
                       let uu____1493 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.print1 "Reduced tactic: got %s\n"
                         uu____1493) in
                FStar_Tactics_Basic.bind uu____1483
                  (fun uu____1499  ->
                     let uu____1500 =
                       FStar_Tactics_Embedding.unembed_result proof_state
                         result unembed_b in
                     match uu____1500 with
                     | FStar_Util.Inl (b,ps) ->
                         let uu____1525 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1525
                           (fun uu____1529  -> FStar_Tactics_Basic.ret b)
                     | FStar_Util.Inr (msg,ps) ->
                         let uu____1540 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1540
                           (fun uu____1544  -> FStar_Tactics_Basic.fail msg))))
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
        let uu____1569 =
          FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic in
        match uu____1569 with
        | (tactic1,uu____1583,uu____1584) ->
            let tau =
              unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1 in
            let uu____1588 = FStar_TypeChecker_Env.clear_expected_typ env in
            (match uu____1588 with
             | (env1,uu____1602) ->
                 let env2 =
                   let uu___133_1608 = env1 in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___133_1608.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___133_1608.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___133_1608.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___133_1608.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___133_1608.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___133_1608.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___133_1608.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___133_1608.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___133_1608.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp = false;
                     FStar_TypeChecker_Env.effects =
                       (uu___133_1608.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___133_1608.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___133_1608.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___133_1608.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___133_1608.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___133_1608.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___133_1608.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___133_1608.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (uu___133_1608.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___133_1608.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.failhard =
                       (uu___133_1608.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___133_1608.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.type_of =
                       (uu___133_1608.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___133_1608.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___133_1608.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qname_and_index =
                       (uu___133_1608.FStar_TypeChecker_Env.qname_and_index);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___133_1608.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth =
                       (uu___133_1608.FStar_TypeChecker_Env.synth);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___133_1608.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___133_1608.FStar_TypeChecker_Env.identifier_info)
                   } in
                 let uu____1609 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
                 (match uu____1609 with
                  | (ps,w) ->
                      let uu____1622 = FStar_Tactics_Basic.run tau ps in
                      (match uu____1622 with
                       | FStar_Tactics_Result.Success (uu____1631,ps1) ->
                           ((let uu____1634 = FStar_ST.op_Bang tacdbg in
                             if uu____1634
                             then
                               let uu____1645 =
                                 FStar_Syntax_Print.term_to_string w in
                               FStar_Util.print1
                                 "Tactic generated proofterm %s\n" uu____1645
                             else ());
                            FStar_List.iter
                              (fun g  ->
                                 let uu____1652 =
                                   FStar_Tactics_Basic.is_irrelevant g in
                                 if uu____1652
                                 then
                                   let uu____1653 =
                                     FStar_TypeChecker_Rel.teq_nosmt
                                       g.FStar_Tactics_Types.context
                                       g.FStar_Tactics_Types.witness
                                       FStar_Syntax_Util.exp_unit in
                                   (if uu____1653
                                    then ()
                                    else
                                      (let uu____1655 =
                                         let uu____1656 =
                                           FStar_Syntax_Print.term_to_string
                                             g.FStar_Tactics_Types.witness in
                                         FStar_Util.format1
                                           "Irrelevant tactic witness does not unify with (): %s"
                                           uu____1656 in
                                       failwith uu____1655))
                                 else ())
                              (FStar_List.append
                                 ps1.FStar_Tactics_Types.goals
                                 ps1.FStar_Tactics_Types.smt_goals);
                            (let g =
                               let uu___134_1659 =
                                 FStar_TypeChecker_Rel.trivial_guard in
                               {
                                 FStar_TypeChecker_Env.guard_f =
                                   (uu___134_1659.FStar_TypeChecker_Env.guard_f);
                                 FStar_TypeChecker_Env.deferred =
                                   (uu___134_1659.FStar_TypeChecker_Env.deferred);
                                 FStar_TypeChecker_Env.univ_ineqs =
                                   (uu___134_1659.FStar_TypeChecker_Env.univ_ineqs);
                                 FStar_TypeChecker_Env.implicits =
                                   (ps1.FStar_Tactics_Types.all_implicits)
                               } in
                             let g1 =
                               let uu____1661 =
                                 FStar_TypeChecker_Rel.solve_deferred_constraints
                                   env2 g in
                               FStar_All.pipe_right uu____1661
                                 FStar_TypeChecker_Rel.resolve_implicits_lax in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               g1;
                             ((FStar_List.append
                                 ps1.FStar_Tactics_Types.goals
                                 ps1.FStar_Tactics_Types.smt_goals), w)))
                       | FStar_Tactics_Result.Failed (s,ps1) ->
                           (FStar_Tactics_Basic.dump_proofstate ps1
                              "at the time of failure";
                            (let uu____1668 =
                               let uu____1669 =
                                 let uu____1674 =
                                   FStar_Util.format1
                                     "user tactic failed: %s" s in
                                 (uu____1674, (typ.FStar_Syntax_Syntax.pos)) in
                               FStar_Errors.Error uu____1669 in
                             FStar_Exn.raise uu____1668)))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1685 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1690 -> false
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
        let uu____1719 = FStar_Syntax_Util.head_and_args t in
        match uu____1719 with
        | (hd1,args) ->
            let uu____1762 =
              let uu____1775 =
                let uu____1776 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1776.FStar_Syntax_Syntax.n in
              (uu____1775, args) in
            (match uu____1762 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1795))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1864 = run_tactic_on_typ tactic e assertion in
                   (match uu____1864 with
                    | (gs,uu____1878) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____1930 =
                     let uu____1933 =
                       let uu____1934 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____1934 in
                     [uu____1933] in
                   (FStar_Syntax_Util.t_true, uu____1930)
                 else (assertion, [])
             | uu____1950 -> (t, []))
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
          let uu____2020 =
            let uu____2027 =
              let uu____2028 = FStar_Syntax_Subst.compress t in
              uu____2028.FStar_Syntax_Syntax.n in
            match uu____2027 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2043 = traverse f pol e t1 in
                (match uu____2043 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____2070 = traverse f pol e t1 in
                (match uu____2070 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2092;
                   FStar_Syntax_Syntax.vars = uu____2093;_},(p,uu____2095)::
                 (q,uu____2097)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2137 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2137 in
                let uu____2138 = traverse f (flip pol) e p in
                (match uu____2138 with
                 | (p',gs1) ->
                     let uu____2157 =
                       let uu____2164 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____2164 q in
                     (match uu____2157 with
                      | (q',gs2) ->
                          let uu____2177 =
                            let uu____2178 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____2178.FStar_Syntax_Syntax.n in
                          (uu____2177, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____2205 = traverse f pol e hd1 in
                (match uu____2205 with
                 | (hd',gs1) ->
                     let uu____2224 =
                       FStar_List.fold_right
                         (fun uu____2262  ->
                            fun uu____2263  ->
                              match (uu____2262, uu____2263) with
                              | ((a,q),(as',gs)) ->
                                  let uu____2344 = traverse f pol e a in
                                  (match uu____2344 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____2224 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2448 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2448 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2462 =
                       let uu____2477 =
                         FStar_List.map
                           (fun uu____2510  ->
                              match uu____2510 with
                              | (bv,aq) ->
                                  let uu____2527 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2527 with
                                   | (s',gs) ->
                                       (((let uu___135_2557 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___135_2557.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___135_2557.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2477 in
                     (match uu____2462 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2621 = traverse f pol e' topen in
                          (match uu____2621 with
                           | (topen',gs2) ->
                               let uu____2640 =
                                 let uu____2641 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2641.FStar_Syntax_Syntax.n in
                               (uu____2640, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2020 with
          | (tn',gs) ->
              let t' =
                let uu___136_2664 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___136_2664.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___136_2664.FStar_Syntax_Syntax.vars)
                } in
              let uu____2665 = f pol e t' in
              (match uu____2665 with
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
      (let uu____2724 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____2724);
      (let uu____2736 = FStar_ST.op_Bang tacdbg in
       if uu____2736
       then
         let uu____2747 =
           let uu____2748 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2748
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2749 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2747
           uu____2749
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2778 = traverse by_tactic_interp Pos env goal in
       match uu____2778 with
       | (t',gs) ->
           ((let uu____2800 = FStar_ST.op_Bang tacdbg in
             if uu____2800
             then
               let uu____2811 =
                 let uu____2812 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2812
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2813 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2811 uu____2813
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2860  ->
                    fun g  ->
                      match uu____2860 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2905 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____2905 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____2908 =
                                  let uu____2909 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2909 in
                                failwith uu____2908
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____2912 = FStar_ST.op_Bang tacdbg in
                            if uu____2912
                            then
                              let uu____2923 = FStar_Util.string_of_int n1 in
                              let uu____2924 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2923 uu____2924
                            else ());
                           (let gt' =
                              let uu____2927 =
                                let uu____2928 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____2928 in
                              FStar_TypeChecker_Util.label uu____2927
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____2943 = s1 in
             match uu____2943 with
             | (uu____2964,gs1) ->
                 let uu____2982 =
                   let uu____2989 = FStar_Options.peek () in
                   (env, t', uu____2989) in
                 uu____2982 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____3001 =
        let uu____3002 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____3002 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3001 [FStar_Syntax_Syntax.U_zero] in
    let uu____3003 =
      let uu____3004 =
        let uu____3005 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____3006 =
          let uu____3009 = FStar_Syntax_Syntax.as_arg a in [uu____3009] in
        uu____3005 :: uu____3006 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3004 in
    uu____3003 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____3025 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____3025);
        (let uu____3036 =
           let uu____3043 = reify_tactic tau in
           run_tactic_on_typ uu____3043 env typ in
         match uu____3036 with
         | (gs,w) ->
             let uu____3050 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____3054 =
                      let uu____3055 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____3055 in
                    Prims.op_Negation uu____3054) gs in
             if uu____3050
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)