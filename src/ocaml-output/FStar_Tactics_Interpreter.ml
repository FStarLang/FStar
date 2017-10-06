open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let mk_tactic_interpretation_0:
  'a .
    'a FStar_Tactics_Basic.tac ->
      ('a -> FStar_Syntax_Syntax.term) ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lid ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun embed_a  ->
      fun t_a  ->
        fun nm  ->
          fun args  ->
            match args with
            | (embedded_state,uu____55)::[] ->
                let ps =
                  FStar_Tactics_Embedding.unembed_proofstate embedded_state in
                (FStar_Tactics_Basic.log ps
                   (fun uu____77  ->
                      let uu____78 = FStar_Ident.string_of_lid nm in
                      let uu____79 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.print2 "Reached %s, args are: %s\n" uu____78
                        uu____79);
                 (let res = FStar_Tactics_Basic.run t ps in
                  let uu____83 =
                    FStar_Tactics_Embedding.embed_result ps res embed_a t_a in
                  FStar_Pervasives_Native.Some uu____83))
            | uu____84 ->
                failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1:
  'a 'b .
    ('b -> 'a FStar_Tactics_Basic.tac) ->
      (FStar_Syntax_Syntax.term -> 'b) ->
        ('a -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_b  ->
      fun embed_a  ->
        fun t_a  ->
          fun nm  ->
            fun args  ->
              match args with
              | (b,uu____151)::(embedded_state,uu____153)::[] ->
                  let ps =
                    FStar_Tactics_Embedding.unembed_proofstate embedded_state in
                  (FStar_Tactics_Basic.log ps
                     (fun uu____185  ->
                        let uu____186 = FStar_Ident.string_of_lid nm in
                        let uu____187 =
                          FStar_Syntax_Print.term_to_string embedded_state in
                        FStar_Util.print2 "Reached %s, goals are: %s\n"
                          uu____186 uu____187);
                   (let res =
                      let uu____191 =
                        let uu____194 = unembed_b b in t uu____194 in
                      FStar_Tactics_Basic.run uu____191 ps in
                    let uu____195 =
                      FStar_Tactics_Embedding.embed_result ps res embed_a t_a in
                    FStar_Pervasives_Native.Some uu____195))
              | uu____196 ->
                  let uu____197 =
                    let uu____198 = FStar_Ident.string_of_lid nm in
                    let uu____199 = FStar_Syntax_Print.args_to_string args in
                    FStar_Util.format2
                      "Unexpected application of tactic primitive %s %s"
                      uu____198 uu____199 in
                  failwith uu____197
let mk_tactic_interpretation_2:
  'a 'b 'c .
    ('a -> 'b -> 'c FStar_Tactics_Basic.tac) ->
      (FStar_Syntax_Syntax.term -> 'a) ->
        (FStar_Syntax_Syntax.term -> 'b) ->
          ('c -> FStar_Syntax_Syntax.term) ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun embed_c  ->
          fun t_c  ->
            fun nm  ->
              fun args  ->
                match args with
                | (a,uu____285)::(b,uu____287)::(embedded_state,uu____289)::[]
                    ->
                    let ps =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    (FStar_Tactics_Basic.log ps
                       (fun uu____331  ->
                          let uu____332 = FStar_Ident.string_of_lid nm in
                          let uu____333 =
                            FStar_Syntax_Print.term_to_string embedded_state in
                          FStar_Util.print2 "Reached %s, goals are: %s\n"
                            uu____332 uu____333);
                     (let res =
                        let uu____337 =
                          let uu____340 = unembed_a a in
                          let uu____341 = unembed_b b in
                          t uu____340 uu____341 in
                        FStar_Tactics_Basic.run uu____337 ps in
                      let uu____342 =
                        FStar_Tactics_Embedding.embed_result ps res embed_c
                          t_c in
                      FStar_Pervasives_Native.Some uu____342))
                | uu____343 ->
                    let uu____344 =
                      let uu____345 = FStar_Ident.string_of_lid nm in
                      let uu____346 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____345 uu____346 in
                    failwith uu____344
let mk_tactic_interpretation_3:
  'a 'b 'c 'd .
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
  fun t  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun unembed_c  ->
          fun embed_d  ->
            fun t_d  ->
              fun nm  ->
                fun args  ->
                  match args with
                  | (a,uu____451)::(b,uu____453)::(c,uu____455)::(embedded_state,uu____457)::[]
                      ->
                      let ps =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      (FStar_Tactics_Basic.log ps
                         (fun uu____509  ->
                            let uu____510 = FStar_Ident.string_of_lid nm in
                            let uu____511 =
                              FStar_Syntax_Print.term_to_string
                                embedded_state in
                            FStar_Util.print2 "Reached %s, goals are: %s\n"
                              uu____510 uu____511);
                       (let res =
                          let uu____515 =
                            let uu____518 = unembed_a a in
                            let uu____519 = unembed_b b in
                            let uu____520 = unembed_c c in
                            t uu____518 uu____519 uu____520 in
                          FStar_Tactics_Basic.run uu____515 ps in
                        let uu____521 =
                          FStar_Tactics_Embedding.embed_result ps res embed_d
                            t_d in
                        FStar_Pervasives_Native.Some uu____521))
                  | uu____522 ->
                      let uu____523 =
                        let uu____524 = FStar_Ident.string_of_lid nm in
                        let uu____525 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____524 uu____525 in
                      failwith uu____523
let mk_tactic_interpretation_5:
  'a 'b 'c 'd 'e 'f .
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
                      | (a,uu____668)::(b,uu____670)::(c,uu____672)::
                          (d,uu____674)::(e,uu____676)::(embedded_state,uu____678)::[]
                          ->
                          let ps =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state in
                          (FStar_Tactics_Basic.log ps
                             (fun uu____750  ->
                                let uu____751 = FStar_Ident.string_of_lid nm in
                                let uu____752 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____751
                                  uu____752);
                           (let res =
                              let uu____756 =
                                let uu____759 = unembed_a a in
                                let uu____760 = unembed_b b in
                                let uu____761 = unembed_c c in
                                let uu____762 = unembed_d d in
                                let uu____763 = unembed_e e in
                                t uu____759 uu____760 uu____761 uu____762
                                  uu____763 in
                              FStar_Tactics_Basic.run uu____756 ps in
                            let uu____764 =
                              FStar_Tactics_Embedding.embed_result ps res
                                embed_f t_f in
                            FStar_Pervasives_Native.Some uu____764))
                      | uu____765 ->
                          let uu____766 =
                            let uu____767 = FStar_Ident.string_of_lid nm in
                            let uu____768 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____767 uu____768 in
                          failwith uu____766
let step_from_native_step:
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step
  =
  fun s  ->
    {
      FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
      FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
      FStar_TypeChecker_Normalize.strong_reduction_ok =
        (s.FStar_Tactics_Native.strong_reduction_ok);
      FStar_TypeChecker_Normalize.interpretation =
        (fun _rng  -> fun args  -> s.FStar_Tactics_Native.tactic args)
    }
let rec primitive_steps:
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list =
  fun uu____798  ->
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
      FStar_List.map step_from_native_step native_tactics in
    let mktac0 name f e_a ta =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 f e_a ta) in
    let mktac1 name f u_a e_b tb =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 f u_a e_b tb) in
    let mktac2 name f u_a u_b e_c tc =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 f u_a u_b e_c tc) in
    let mktac3 name f u_a u_b u_c e_d tc =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 f u_a u_b u_c e_d tc) in
    let mktac5 name f u_a u_b u_c u_d u_e e_f tc =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 f u_a u_b u_c u_d u_e e_f tc) in
    let decr_depth_interp rng args =
      match args with
      | (ps,uu____1195)::[] ->
          let uu____1212 =
            let uu____1213 =
              let uu____1214 = FStar_Tactics_Embedding.unembed_proofstate ps in
              FStar_Tactics_Types.decr_depth uu____1214 in
            FStar_Tactics_Embedding.embed_proofstate uu____1213 in
          FStar_Pervasives_Native.Some uu____1212
      | uu____1215 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1219 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1219;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp rng args =
      match args with
      | (ps,uu____1232)::[] ->
          let uu____1249 =
            let uu____1250 =
              let uu____1251 = FStar_Tactics_Embedding.unembed_proofstate ps in
              FStar_Tactics_Types.incr_depth uu____1251 in
            FStar_Tactics_Embedding.embed_proofstate uu____1250 in
          FStar_Pervasives_Native.Some uu____1249
      | uu____1252 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1256 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1256;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp rng args =
      match args with
      | (ps,uu____1273)::[] ->
          ((let uu____1291 = FStar_Tactics_Embedding.unembed_proofstate ps in
            FStar_Tactics_Types.tracepoint uu____1291);
           FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1294 -> failwith "Unexpected application of tracepoint" in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let uu____1301 =
      let uu____1304 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
      let uu____1305 =
        let uu____1308 =
          mktac2 "__trytac" (fun uu____1314  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Syntax_Embeddings.embed_option (fun t  -> t)
               FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit in
        let uu____1321 =
          let uu____1324 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1325 =
            let uu____1328 =
              let uu____1329 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Syntax_Embeddings.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1329 in
            let uu____1334 =
              let uu____1337 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Syntax_Embeddings.unembed_list
                     FStar_Syntax_Embeddings.unembed_norm_step)
                  FStar_Syntax_Embeddings.embed_unit
                  FStar_Syntax_Syntax.t_unit in
              let uu____1340 =
                let uu____1343 =
                  mktac2 "__norm_term" FStar_Tactics_Basic.norm_term
                    (FStar_Syntax_Embeddings.unembed_list
                       FStar_Syntax_Embeddings.unembed_norm_step)
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_term
                    FStar_Syntax_Syntax.t_term in
                let uu____1346 =
                  let uu____1349 =
                    mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Syntax_Embeddings.unembed_string
                      FStar_Syntax_Embeddings.embed_unit
                      FStar_Syntax_Syntax.t_unit in
                  let uu____1350 =
                    let uu____1353 =
                      mktac1 "__binder_retype"
                        FStar_Tactics_Basic.binder_retype
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1354 =
                      let uu____1357 =
                        mktac0 "__revert" FStar_Tactics_Basic.revert
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____1358 =
                        let uu____1361 =
                          mktac0 "__clear_top" FStar_Tactics_Basic.clear_top
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____1362 =
                          let uu____1365 =
                            mktac1 "__clear" FStar_Tactics_Basic.clear
                              FStar_Reflection_Basic.unembed_binder
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____1366 =
                            let uu____1369 =
                              mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                                FStar_Reflection_Basic.unembed_binder
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____1370 =
                              let uu____1373 =
                                mktac0 "__smt" FStar_Tactics_Basic.smt
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____1374 =
                                let uu____1377 =
                                  mktac1 "__exact" FStar_Tactics_Basic.exact
                                    FStar_Reflection_Basic.unembed_term
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____1378 =
                                  let uu____1381 =
                                    mktac1 "__exact_lemma"
                                      FStar_Tactics_Basic.exact_lemma
                                      FStar_Reflection_Basic.unembed_term
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____1382 =
                                    let uu____1385 =
                                      mktac1 "__apply"
                                        (FStar_Tactics_Basic.apply true)
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____1386 =
                                      let uu____1389 =
                                        mktac1 "__apply_raw"
                                          (FStar_Tactics_Basic.apply false)
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____1390 =
                                        let uu____1393 =
                                          mktac1 "__apply_lemma"
                                            FStar_Tactics_Basic.apply_lemma
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____1394 =
                                          let uu____1397 =
                                            mktac5 "__divide"
                                              (fun uu____1408  ->
                                                 fun uu____1409  ->
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
                                          let uu____1422 =
                                            let uu____1425 =
                                              mktac1 "__set_options"
                                                FStar_Tactics_Basic.set_options
                                                FStar_Syntax_Embeddings.unembed_string
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____1426 =
                                              let uu____1429 =
                                                mktac2 "__seq"
                                                  FStar_Tactics_Basic.seq
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  FStar_Syntax_Embeddings.embed_unit
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____1434 =
                                                let uu____1437 =
                                                  mktac2 "__unquote"
                                                    FStar_Tactics_Basic.unquote
                                                    (fun t  -> t)
                                                    FStar_Reflection_Basic.unembed_term
                                                    (fun t  -> t)
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____1442 =
                                                  let uu____1445 =
                                                    mktac1 "__prune"
                                                      FStar_Tactics_Basic.prune
                                                      FStar_Syntax_Embeddings.unembed_string
                                                      FStar_Syntax_Embeddings.embed_unit
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____1446 =
                                                    let uu____1449 =
                                                      mktac1 "__addns"
                                                        FStar_Tactics_Basic.addns
                                                        FStar_Syntax_Embeddings.unembed_string
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____1450 =
                                                      let uu____1453 =
                                                        mktac1 "__print"
                                                          (fun x  ->
                                                             FStar_Tactics_Basic.tacprint
                                                               x;
                                                             FStar_Tactics_Basic.ret
                                                               ())
                                                          FStar_Syntax_Embeddings.unembed_string
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____1458 =
                                                        let uu____1461 =
                                                          mktac1 "__dump"
                                                            FStar_Tactics_Basic.print_proof_state
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____1462 =
                                                          let uu____1465 =
                                                            mktac1 "__dump1"
                                                              FStar_Tactics_Basic.print_proof_state1
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____1466 =
                                                            let uu____1469 =
                                                              mktac2
                                                                "__pointwise"
                                                                FStar_Tactics_Basic.pointwise
                                                                FStar_Tactics_Embedding.unembed_direction
                                                                (unembed_tactic_0
                                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____1472 =
                                                              let uu____1475
                                                                =
                                                                mktac0
                                                                  "__trefl"
                                                                  FStar_Tactics_Basic.trefl
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____1476
                                                                =
                                                                let uu____1479
                                                                  =
                                                                  mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____1480
                                                                  =
                                                                  let uu____1483
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____1484
                                                                    =
                                                                    let uu____1487
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1488
                                                                    =
                                                                    let uu____1491
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1492
                                                                    =
                                                                    let uu____1495
                                                                    =
                                                                    let uu____1496
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    (FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term)
                                                                    uu____1496 in
                                                                    let uu____1501
                                                                    =
                                                                    let uu____1504
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1505
                                                                    =
                                                                    let uu____1508
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1509
                                                                    =
                                                                    let uu____1512
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1513
                                                                    =
                                                                    let uu____1516
                                                                    =
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    (FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1519
                                                                    =
                                                                    let uu____1522
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____1523
                                                                    =
                                                                    let uu____1526
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____1526;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step] in
                                                                    uu____1522
                                                                    ::
                                                                    uu____1523 in
                                                                    uu____1516
                                                                    ::
                                                                    uu____1519 in
                                                                    uu____1512
                                                                    ::
                                                                    uu____1513 in
                                                                    uu____1508
                                                                    ::
                                                                    uu____1509 in
                                                                    uu____1504
                                                                    ::
                                                                    uu____1505 in
                                                                    uu____1495
                                                                    ::
                                                                    uu____1501 in
                                                                    uu____1491
                                                                    ::
                                                                    uu____1492 in
                                                                    uu____1487
                                                                    ::
                                                                    uu____1488 in
                                                                  uu____1483
                                                                    ::
                                                                    uu____1484 in
                                                                uu____1479 ::
                                                                  uu____1480 in
                                                              uu____1475 ::
                                                                uu____1476 in
                                                            uu____1469 ::
                                                              uu____1472 in
                                                          uu____1465 ::
                                                            uu____1466 in
                                                        uu____1461 ::
                                                          uu____1462 in
                                                      uu____1453 ::
                                                        uu____1458 in
                                                    uu____1449 :: uu____1450 in
                                                  uu____1445 :: uu____1446 in
                                                uu____1437 :: uu____1442 in
                                              uu____1429 :: uu____1434 in
                                            uu____1425 :: uu____1426 in
                                          uu____1397 :: uu____1422 in
                                        uu____1393 :: uu____1394 in
                                      uu____1389 :: uu____1390 in
                                    uu____1385 :: uu____1386 in
                                  uu____1381 :: uu____1382 in
                                uu____1377 :: uu____1378 in
                              uu____1373 :: uu____1374 in
                            uu____1369 :: uu____1370 in
                          uu____1365 :: uu____1366 in
                        uu____1361 :: uu____1362 in
                      uu____1357 :: uu____1358 in
                    uu____1353 :: uu____1354 in
                  uu____1349 :: uu____1350 in
                uu____1343 :: uu____1346 in
              uu____1337 :: uu____1340 in
            uu____1328 :: uu____1334 in
          uu____1324 :: uu____1325 in
        uu____1308 :: uu____1321 in
      uu____1304 :: uu____1305 in
    FStar_List.append uu____1301
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
             let uu____1545 =
               let uu____1546 =
                 let uu____1547 =
                   let uu____1548 =
                     FStar_Tactics_Embedding.embed_proofstate proof_state in
                   FStar_Syntax_Syntax.as_arg uu____1548 in
                 [uu____1547] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1546 in
             uu____1545 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let steps =
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____1555 = FStar_ST.op_Bang tacdbg in
            if uu____1555
            then
              let uu____1602 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1602
            else ());
           (let result =
              let uu____1605 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1605 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____1609 = FStar_ST.op_Bang tacdbg in
             if uu____1609
             then
               let uu____1656 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____1656
             else ());
            (let uu____1658 =
               FStar_Tactics_Embedding.unembed_result proof_state result
                 unembed_b in
             match uu____1658 with
             | FStar_Util.Inl (b,ps) ->
                 let uu____1683 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____1683
                   (fun uu____1687  -> FStar_Tactics_Basic.ret b)
             | FStar_Util.Inr (msg,ps) ->
                 let uu____1698 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____1698
                   (fun uu____1702  -> FStar_Tactics_Basic.fail msg))))
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
        (let uu____1728 = FStar_ST.op_Bang tacdbg in
         if uu____1728
         then
           let uu____1775 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____1775
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         (let uu____1779 = FStar_ST.op_Bang tacdbg in
          if uu____1779
          then
            let uu____1826 = FStar_Syntax_Print.term_to_string tactic1 in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____1826
          else ());
         (let uu____1828 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1 in
          match uu____1828 with
          | (tactic2,uu____1842,uu____1843) ->
              let tau =
                unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic2 in
              let uu____1847 = FStar_TypeChecker_Env.clear_expected_typ env in
              (match uu____1847 with
               | (env1,uu____1861) ->
                   let env2 =
                     let uu___155_1867 = env1 in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___155_1867.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___155_1867.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___155_1867.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___155_1867.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___155_1867.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___155_1867.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___155_1867.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___155_1867.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___155_1867.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp = false;
                       FStar_TypeChecker_Env.effects =
                         (uu___155_1867.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___155_1867.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___155_1867.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___155_1867.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___155_1867.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___155_1867.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___155_1867.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___155_1867.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___155_1867.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___155_1867.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___155_1867.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___155_1867.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___155_1867.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___155_1867.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___155_1867.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___155_1867.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___155_1867.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___155_1867.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___155_1867.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___155_1867.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___155_1867.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___155_1867.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___155_1867.FStar_TypeChecker_Env.dsenv)
                     } in
                   let uu____1868 =
                     FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
                   (match uu____1868 with
                    | (ps,w) ->
                        let uu____1881 = FStar_Tactics_Basic.run tau ps in
                        (match uu____1881 with
                         | FStar_Tactics_Result.Success (uu____1890,ps1) ->
                             ((let uu____1893 = FStar_ST.op_Bang tacdbg in
                               if uu____1893
                               then
                                 let uu____1940 =
                                   FStar_Syntax_Print.term_to_string w in
                                 FStar_Util.print1
                                   "Tactic generated proofterm %s\n"
                                   uu____1940
                               else ());
                              FStar_List.iter
                                (fun g  ->
                                   let uu____1947 =
                                     FStar_Tactics_Basic.is_irrelevant g in
                                   if uu____1947
                                   then
                                     let uu____1948 =
                                       FStar_TypeChecker_Rel.teq_nosmt
                                         g.FStar_Tactics_Types.context
                                         g.FStar_Tactics_Types.witness
                                         FStar_Syntax_Util.exp_unit in
                                     (if uu____1948
                                      then ()
                                      else
                                        (let uu____1950 =
                                           let uu____1951 =
                                             FStar_Syntax_Print.term_to_string
                                               g.FStar_Tactics_Types.witness in
                                           FStar_Util.format1
                                             "Irrelevant tactic witness does not unify with (): %s"
                                             uu____1951 in
                                         failwith uu____1950))
                                   else ())
                                (FStar_List.append
                                   ps1.FStar_Tactics_Types.goals
                                   ps1.FStar_Tactics_Types.smt_goals);
                              (let g =
                                 let uu___156_1954 =
                                   FStar_TypeChecker_Rel.trivial_guard in
                                 {
                                   FStar_TypeChecker_Env.guard_f =
                                     (uu___156_1954.FStar_TypeChecker_Env.guard_f);
                                   FStar_TypeChecker_Env.deferred =
                                     (uu___156_1954.FStar_TypeChecker_Env.deferred);
                                   FStar_TypeChecker_Env.univ_ineqs =
                                     (uu___156_1954.FStar_TypeChecker_Env.univ_ineqs);
                                   FStar_TypeChecker_Env.implicits =
                                     (ps1.FStar_Tactics_Types.all_implicits)
                                 } in
                               let g1 =
                                 let uu____1956 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env2 g in
                                 FStar_All.pipe_right uu____1956
                                   FStar_TypeChecker_Rel.resolve_implicits_tac in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 g1;
                               ((FStar_List.append
                                   ps1.FStar_Tactics_Types.goals
                                   ps1.FStar_Tactics_Types.smt_goals), w)))
                         | FStar_Tactics_Result.Failed (s,ps1) ->
                             (FStar_Tactics_Basic.dump_proofstate ps1
                                "at the time of failure";
                              (let uu____1963 =
                                 let uu____1964 =
                                   let uu____1969 =
                                     FStar_Util.format1
                                       "user tactic failed: %s" s in
                                   (uu____1969,
                                     (typ.FStar_Syntax_Syntax.pos)) in
                                 FStar_Errors.Error uu____1964 in
                               FStar_Exn.raise uu____1963)))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1980 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1985 -> false
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
        let uu____2014 = FStar_Syntax_Util.head_and_args t in
        match uu____2014 with
        | (hd1,args) ->
            let uu____2057 =
              let uu____2070 =
                let uu____2071 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2071.FStar_Syntax_Syntax.n in
              (uu____2070, args) in
            (match uu____2057 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2090))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2159 = run_tactic_on_typ tactic e assertion in
                   (match uu____2159 with
                    | (gs,uu____2173) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2225 =
                     let uu____2228 =
                       let uu____2229 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____2229 in
                     [uu____2228] in
                   (FStar_Syntax_Util.t_true, uu____2225)
                 else (assertion, [])
             | uu____2245 -> (t, []))
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
          let uu____2315 =
            let uu____2322 =
              let uu____2323 = FStar_Syntax_Subst.compress t in
              uu____2323.FStar_Syntax_Syntax.n in
            match uu____2322 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2338 = traverse f pol e t1 in
                (match uu____2338 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____2365 = traverse f pol e t1 in
                (match uu____2365 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2387;
                   FStar_Syntax_Syntax.vars = uu____2388;_},(p,uu____2390)::
                 (q,uu____2392)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2432 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2432 in
                let uu____2433 = traverse f (flip pol) e p in
                (match uu____2433 with
                 | (p',gs1) ->
                     let uu____2452 =
                       let uu____2459 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____2459 q in
                     (match uu____2452 with
                      | (q',gs2) ->
                          let uu____2472 =
                            let uu____2473 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____2473.FStar_Syntax_Syntax.n in
                          (uu____2472, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____2500 = traverse f pol e hd1 in
                (match uu____2500 with
                 | (hd',gs1) ->
                     let uu____2519 =
                       FStar_List.fold_right
                         (fun uu____2557  ->
                            fun uu____2558  ->
                              match (uu____2557, uu____2558) with
                              | ((a,q),(as',gs)) ->
                                  let uu____2639 = traverse f pol e a in
                                  (match uu____2639 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____2519 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2743 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2743 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2757 =
                       let uu____2772 =
                         FStar_List.map
                           (fun uu____2805  ->
                              match uu____2805 with
                              | (bv,aq) ->
                                  let uu____2822 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____2822 with
                                   | (s',gs) ->
                                       (((let uu___157_2852 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___157_2852.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___157_2852.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2772 in
                     (match uu____2757 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2916 = traverse f pol e' topen in
                          (match uu____2916 with
                           | (topen',gs2) ->
                               let uu____2935 =
                                 let uu____2936 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2936.FStar_Syntax_Syntax.n in
                               (uu____2935, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2315 with
          | (tn',gs) ->
              let t' =
                let uu___158_2959 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___158_2959.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___158_2959.FStar_Syntax_Syntax.vars)
                } in
              let uu____2960 = f pol e t' in
              (match uu____2960 with
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
      (let uu____3019 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3019);
      (let uu____3067 = FStar_ST.op_Bang tacdbg in
       if uu____3067
       then
         let uu____3114 =
           let uu____3115 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____3115
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____3116 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3114
           uu____3116
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____3145 = traverse by_tactic_interp Pos env goal in
       match uu____3145 with
       | (t',gs) ->
           ((let uu____3167 = FStar_ST.op_Bang tacdbg in
             if uu____3167
             then
               let uu____3214 =
                 let uu____3215 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____3215
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____3216 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3214 uu____3216
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3263  ->
                    fun g  ->
                      match uu____3263 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3308 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____3308 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3311 =
                                  let uu____3312 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____3312 in
                                failwith uu____3311
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____3315 = FStar_ST.op_Bang tacdbg in
                            if uu____3315
                            then
                              let uu____3362 = FStar_Util.string_of_int n1 in
                              let uu____3363 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3362 uu____3363
                            else ());
                           (let gt' =
                              let uu____3366 =
                                let uu____3367 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____3367 in
                              FStar_TypeChecker_Util.label uu____3366
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____3382 = s1 in
             match uu____3382 with
             | (uu____3403,gs1) ->
                 let uu____3421 =
                   let uu____3428 = FStar_Options.peek () in
                   (env, t', uu____3428) in
                 uu____3421 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____3440 =
        let uu____3441 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____3441 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3440 [FStar_Syntax_Syntax.U_zero] in
    let uu____3442 =
      let uu____3443 =
        let uu____3444 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____3445 =
          let uu____3448 = FStar_Syntax_Syntax.as_arg a in [uu____3448] in
        uu____3444 :: uu____3445 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3443 in
    uu____3442 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____3464 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____3464);
        (let uu____3511 =
           let uu____3518 = reify_tactic tau in
           run_tactic_on_typ uu____3518 env typ in
         match uu____3511 with
         | (gs,w) ->
             let uu____3525 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____3529 =
                      let uu____3530 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____3530 in
                    Prims.op_Negation uu____3529) gs in
             if uu____3525
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)