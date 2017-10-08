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
let mk_tactic_interpretation_1_env:
  'a 'b .
    FStar_Tactics_Types.proofstate ->
      (FStar_TypeChecker_Normalize.psc -> 'b -> 'a FStar_Tactics_Basic.tac)
        ->
        (FStar_Syntax_Syntax.term -> 'b) ->
          ('a -> FStar_Syntax_Syntax.term) ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun t  ->
      fun unembed_b  ->
        fun embed_a  ->
          fun t_a  ->
            fun nm  ->
              fun ctxt  ->
                fun args  ->
                  match args with
                  | (b,uu____295)::(embedded_state,uu____297)::[] ->
                      (FStar_Tactics_Basic.log ps
                         (fun uu____328  ->
                            let uu____329 = FStar_Ident.string_of_lid nm in
                            let uu____330 =
                              FStar_Syntax_Print.term_to_string
                                embedded_state in
                            FStar_Util.print2 "Reached %s, goals are: %s\n"
                              uu____329 uu____330);
                       (let ps1 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        let res =
                          let uu____335 =
                            let uu____338 = unembed_b b in t ctxt uu____338 in
                          FStar_Tactics_Basic.run uu____335 ps1 in
                        let uu____339 =
                          FStar_Tactics_Embedding.embed_result ps1 res
                            embed_a t_a in
                        FStar_Pervasives_Native.Some uu____339))
                  | uu____340 ->
                      let uu____341 =
                        let uu____342 = FStar_Ident.string_of_lid nm in
                        let uu____343 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____342 uu____343 in
                      failwith uu____341
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
                  | (a,uu____435)::(b,uu____437)::(embedded_state,uu____439)::[]
                      ->
                      (FStar_Tactics_Basic.log ps
                         (fun uu____480  ->
                            let uu____481 = FStar_Ident.string_of_lid nm in
                            let uu____482 =
                              FStar_Syntax_Print.term_to_string
                                embedded_state in
                            FStar_Util.print2 "Reached %s, goals are: %s\n"
                              uu____481 uu____482);
                       (let ps1 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        let res =
                          let uu____487 =
                            let uu____490 = unembed_a a in
                            let uu____491 = unembed_b b in
                            t uu____490 uu____491 in
                          FStar_Tactics_Basic.run uu____487 ps1 in
                        let uu____492 =
                          FStar_Tactics_Embedding.embed_result ps1 res
                            embed_c t_c in
                        FStar_Pervasives_Native.Some uu____492))
                  | uu____493 ->
                      let uu____494 =
                        let uu____495 = FStar_Ident.string_of_lid nm in
                        let uu____496 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____495 uu____496 in
                      failwith uu____494
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
                    | (a,uu____607)::(b,uu____609)::(c,uu____611)::(embedded_state,uu____613)::[]
                        ->
                        (FStar_Tactics_Basic.log ps
                           (fun uu____664  ->
                              let uu____665 = FStar_Ident.string_of_lid nm in
                              let uu____666 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____665 uu____666);
                         (let ps1 =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state in
                          let res =
                            let uu____671 =
                              let uu____674 = unembed_a a in
                              let uu____675 = unembed_b b in
                              let uu____676 = unembed_c c in
                              t uu____674 uu____675 uu____676 in
                            FStar_Tactics_Basic.run uu____671 ps1 in
                          let uu____677 =
                            FStar_Tactics_Embedding.embed_result ps1 res
                              embed_d t_d in
                          FStar_Pervasives_Native.Some uu____677))
                    | uu____678 ->
                        let uu____679 =
                          let uu____680 = FStar_Ident.string_of_lid nm in
                          let uu____681 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____680 uu____681 in
                        failwith uu____679
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
                        | (a,uu____830)::(b,uu____832)::(c,uu____834)::
                            (d,uu____836)::(e,uu____838)::(embedded_state,uu____840)::[]
                            ->
                            (FStar_Tactics_Basic.log ps
                               (fun uu____911  ->
                                  let uu____912 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____913 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____912
                                    uu____913);
                             (let ps1 =
                                FStar_Tactics_Embedding.unembed_proofstate
                                  embedded_state in
                              let res =
                                let uu____918 =
                                  let uu____921 = unembed_a a in
                                  let uu____922 = unembed_b b in
                                  let uu____923 = unembed_c c in
                                  let uu____924 = unembed_d d in
                                  let uu____925 = unembed_e e in
                                  t uu____921 uu____922 uu____923 uu____924
                                    uu____925 in
                                FStar_Tactics_Basic.run uu____918 ps1 in
                              let uu____926 =
                                FStar_Tactics_Embedding.embed_result ps1 res
                                  embed_f t_f in
                              FStar_Pervasives_Native.Some uu____926))
                        | uu____927 ->
                            let uu____928 =
                              let uu____929 = FStar_Ident.string_of_lid nm in
                              let uu____930 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____929 uu____930 in
                            failwith uu____928
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
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
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
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      } in
    let mk_env nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun ctxt  -> fun args  -> interpretation nm1 ctxt args)
      } in
    let native_tactics = FStar_Tactics_Native.list_all () in
    let native_tactics_steps =
      FStar_List.map (step_from_native_step ps) native_tactics in
    let mktac0 name f e_a ta =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 ps f e_a ta) in
    let mktac1 name f u_a e_b tb =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 ps f u_a e_b tb) in
    let mktac1_env name f u_a e_b tb =
      mk_env name (Prims.parse_int "2")
        (mk_tactic_interpretation_1_env ps f u_a e_b tb) in
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
      | (ps1,uu____1449)::[] ->
          let uu____1466 =
            let uu____1467 =
              let uu____1468 = FStar_Tactics_Embedding.unembed_proofstate ps1 in
              FStar_Tactics_Types.decr_depth uu____1468 in
            FStar_Tactics_Embedding.embed_proofstate uu____1467 in
          FStar_Pervasives_Native.Some uu____1466
      | uu____1469 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1473 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1473;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp rng args =
      match args with
      | (ps1,uu____1486)::[] ->
          let uu____1503 =
            let uu____1504 =
              let uu____1505 = FStar_Tactics_Embedding.unembed_proofstate ps1 in
              FStar_Tactics_Types.incr_depth uu____1505 in
            FStar_Tactics_Embedding.embed_proofstate uu____1504 in
          FStar_Pervasives_Native.Some uu____1503
      | uu____1506 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1510 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1510;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp rng args =
      match args with
      | (ps1,uu____1527)::[] ->
          ((let uu____1545 = FStar_Tactics_Embedding.unembed_proofstate ps1 in
            FStar_Tactics_Types.tracepoint uu____1545);
           FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1548 -> failwith "Unexpected application of tracepoint" in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let uu____1555 =
      let uu____1558 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
      let uu____1559 =
        let uu____1562 =
          mktac2 "__trytac" (fun uu____1568  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Syntax_Embeddings.embed_option (fun t  -> t)
               FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit in
        let uu____1575 =
          let uu____1578 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1579 =
            let uu____1582 =
              let uu____1583 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Syntax_Embeddings.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1583 in
            let uu____1588 =
              let uu____1591 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Syntax_Embeddings.unembed_list
                     FStar_Syntax_Embeddings.unembed_norm_step)
                  FStar_Syntax_Embeddings.embed_unit
                  FStar_Syntax_Syntax.t_unit in
              let uu____1594 =
                let uu____1597 =
                  mktac2 "__norm_term" FStar_Tactics_Basic.norm_term
                    (FStar_Syntax_Embeddings.unembed_list
                       FStar_Syntax_Embeddings.unembed_norm_step)
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_term
                    FStar_Reflection_Data.fstar_refl_term in
                let uu____1600 =
                  let uu____1603 =
                    mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Syntax_Embeddings.unembed_string
                      FStar_Syntax_Embeddings.embed_unit
                      FStar_Syntax_Syntax.t_unit in
                  let uu____1604 =
                    let uu____1607 =
                      mktac1 "__binder_retype"
                        FStar_Tactics_Basic.binder_retype
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1608 =
                      let uu____1611 =
                        mktac0 "__revert" FStar_Tactics_Basic.revert
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____1612 =
                        let uu____1615 =
                          mktac0 "__clear_top" FStar_Tactics_Basic.clear_top
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____1616 =
                          let uu____1619 =
                            mktac1 "__clear" FStar_Tactics_Basic.clear
                              FStar_Reflection_Basic.unembed_binder
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____1620 =
                            let uu____1623 =
                              mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                                FStar_Reflection_Basic.unembed_binder
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____1624 =
                              let uu____1627 =
                                mktac0 "__smt" FStar_Tactics_Basic.smt
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____1628 =
                                let uu____1631 =
                                  mktac1 "__exact" FStar_Tactics_Basic.exact
                                    FStar_Reflection_Basic.unembed_term
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____1632 =
                                  let uu____1635 =
                                    mktac1 "__exact_lemma"
                                      FStar_Tactics_Basic.exact_lemma
                                      FStar_Reflection_Basic.unembed_term
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____1636 =
                                    let uu____1639 =
                                      mktac1 "__apply"
                                        (FStar_Tactics_Basic.apply true)
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____1640 =
                                      let uu____1643 =
                                        mktac1 "__apply_raw"
                                          (FStar_Tactics_Basic.apply false)
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____1644 =
                                        let uu____1647 =
                                          mktac1 "__apply_lemma"
                                            FStar_Tactics_Basic.apply_lemma
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____1648 =
                                          let uu____1651 =
                                            mktac5 "__divide"
                                              (fun uu____1662  ->
                                                 fun uu____1663  ->
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
                                          let uu____1676 =
                                            let uu____1679 =
                                              mktac1 "__set_options"
                                                FStar_Tactics_Basic.set_options
                                                FStar_Syntax_Embeddings.unembed_string
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____1680 =
                                              let uu____1683 =
                                                mktac2 "__seq"
                                                  FStar_Tactics_Basic.seq
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  (unembed_tactic_0
                                                     FStar_Syntax_Embeddings.unembed_unit)
                                                  FStar_Syntax_Embeddings.embed_unit
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____1688 =
                                                let uu____1691 =
                                                  mktac2 "__unquote"
                                                    FStar_Tactics_Basic.unquote
                                                    (fun t  -> t)
                                                    FStar_Reflection_Basic.unembed_term
                                                    (fun t  -> t)
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____1696 =
                                                  let uu____1699 =
                                                    mktac1 "__prune"
                                                      FStar_Tactics_Basic.prune
                                                      FStar_Syntax_Embeddings.unembed_string
                                                      FStar_Syntax_Embeddings.embed_unit
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____1700 =
                                                    let uu____1703 =
                                                      mktac1 "__addns"
                                                        FStar_Tactics_Basic.addns
                                                        FStar_Syntax_Embeddings.unembed_string
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____1704 =
                                                      let uu____1707 =
                                                        mktac1 "__print"
                                                          (fun x  ->
                                                             FStar_Tactics_Basic.tacprint
                                                               x;
                                                             FStar_Tactics_Basic.ret
                                                               ())
                                                          FStar_Syntax_Embeddings.unembed_string
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____1712 =
                                                        let uu____1715 =
                                                          mktac1_env "__dump"
                                                            FStar_Tactics_Basic.print_proof_state
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____1716 =
                                                          let uu____1719 =
                                                            mktac1 "__dump1"
                                                              FStar_Tactics_Basic.print_proof_state1
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____1720 =
                                                            let uu____1723 =
                                                              mktac1
                                                                "__pointwise"
                                                                FStar_Tactics_Basic.pointwise
                                                                (unembed_tactic_0
                                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____1726 =
                                                              let uu____1729
                                                                =
                                                                mktac0
                                                                  "__trefl"
                                                                  FStar_Tactics_Basic.trefl
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____1730
                                                                =
                                                                let uu____1733
                                                                  =
                                                                  mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____1734
                                                                  =
                                                                  let uu____1737
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____1738
                                                                    =
                                                                    let uu____1741
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1742
                                                                    =
                                                                    let uu____1745
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1746
                                                                    =
                                                                    let uu____1749
                                                                    =
                                                                    let uu____1750
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
                                                                    uu____1750 in
                                                                    let uu____1755
                                                                    =
                                                                    let uu____1758
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1759
                                                                    =
                                                                    let uu____1762
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1763
                                                                    =
                                                                    let uu____1766
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1767
                                                                    =
                                                                    let uu____1770
                                                                    =
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    (FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                    let uu____1773
                                                                    =
                                                                    let uu____1776
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____1777
                                                                    =
                                                                    let uu____1780
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____1780;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step] in
                                                                    uu____1776
                                                                    ::
                                                                    uu____1777 in
                                                                    uu____1770
                                                                    ::
                                                                    uu____1773 in
                                                                    uu____1766
                                                                    ::
                                                                    uu____1767 in
                                                                    uu____1762
                                                                    ::
                                                                    uu____1763 in
                                                                    uu____1758
                                                                    ::
                                                                    uu____1759 in
                                                                    uu____1749
                                                                    ::
                                                                    uu____1755 in
                                                                    uu____1745
                                                                    ::
                                                                    uu____1746 in
                                                                    uu____1741
                                                                    ::
                                                                    uu____1742 in
                                                                  uu____1737
                                                                    ::
                                                                    uu____1738 in
                                                                uu____1733 ::
                                                                  uu____1734 in
                                                              uu____1729 ::
                                                                uu____1730 in
                                                            uu____1723 ::
                                                              uu____1726 in
                                                          uu____1719 ::
                                                            uu____1720 in
                                                        uu____1715 ::
                                                          uu____1716 in
                                                      uu____1707 ::
                                                        uu____1712 in
                                                    uu____1703 :: uu____1704 in
                                                  uu____1699 :: uu____1700 in
                                                uu____1691 :: uu____1696 in
                                              uu____1683 :: uu____1688 in
                                            uu____1679 :: uu____1680 in
                                          uu____1651 :: uu____1676 in
                                        uu____1647 :: uu____1648 in
                                      uu____1643 :: uu____1644 in
                                    uu____1639 :: uu____1640 in
                                  uu____1635 :: uu____1636 in
                                uu____1631 :: uu____1632 in
                              uu____1627 :: uu____1628 in
                            uu____1623 :: uu____1624 in
                          uu____1619 :: uu____1620 in
                        uu____1615 :: uu____1616 in
                      uu____1611 :: uu____1612 in
                    uu____1607 :: uu____1608 in
                  uu____1603 :: uu____1604 in
                uu____1597 :: uu____1600 in
              uu____1591 :: uu____1594 in
            uu____1582 :: uu____1588 in
          uu____1578 :: uu____1579 in
        uu____1562 :: uu____1575 in
      uu____1558 :: uu____1559 in
    FStar_List.append uu____1555
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
             let uu____1793 =
               let uu____1794 =
                 let uu____1795 =
                   let uu____1796 =
                     FStar_Tactics_Embedding.embed_proofstate proof_state in
                   FStar_Syntax_Syntax.as_arg uu____1796 in
                 [uu____1795] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1794 in
             uu____1793 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let steps =
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           let uu____1802 =
             FStar_All.pipe_left FStar_Tactics_Basic.mlog
               (fun uu____1811  ->
                  let uu____1812 = FStar_Syntax_Print.term_to_string tm in
                  FStar_Util.print1 "Starting normalizer with %s\n"
                    uu____1812) in
           FStar_Tactics_Basic.bind uu____1802
             (fun uu____1816  ->
                let result =
                  let uu____1818 = primitive_steps proof_state in
                  FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                    uu____1818 steps
                    proof_state.FStar_Tactics_Types.main_context tm in
                let uu____1821 =
                  FStar_All.pipe_left FStar_Tactics_Basic.mlog
                    (fun uu____1830  ->
                       let uu____1831 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.print1 "Reduced tactic: got %s\n"
                         uu____1831) in
                FStar_Tactics_Basic.bind uu____1821
                  (fun uu____1837  ->
                     let uu____1838 =
                       FStar_Tactics_Embedding.unembed_result proof_state
                         result unembed_b in
                     match uu____1838 with
                     | FStar_Util.Inl (b,ps) ->
                         let uu____1863 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1863
                           (fun uu____1867  -> FStar_Tactics_Basic.ret b)
                     | FStar_Util.Inr (msg,ps) ->
                         let uu____1878 = FStar_Tactics_Basic.set ps in
                         FStar_Tactics_Basic.bind uu____1878
                           (fun uu____1882  -> FStar_Tactics_Basic.fail msg))))
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
        (let uu____1908 = FStar_ST.op_Bang tacdbg in
         if uu____1908
         then
           let uu____1955 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____1955
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         (let uu____1959 = FStar_ST.op_Bang tacdbg in
          if uu____1959
          then
            let uu____2006 = FStar_Syntax_Print.term_to_string tactic1 in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2006
          else ());
         (let uu____2008 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1 in
          match uu____2008 with
          | (tactic2,uu____2022,uu____2023) ->
              let tau =
                unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic2 in
              let uu____2027 = FStar_TypeChecker_Env.clear_expected_typ env in
              (match uu____2027 with
               | (env1,uu____2041) ->
                   let env2 =
                     let uu___156_2047 = env1 in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_2047.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_2047.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_2047.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_2047.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_2047.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_2047.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_2047.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_2047.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_2047.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp = false;
                       FStar_TypeChecker_Env.effects =
                         (uu___156_2047.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_2047.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_2047.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_2047.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_2047.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_2047.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_2047.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_2047.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___156_2047.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_2047.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___156_2047.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___156_2047.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___156_2047.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_2047.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_2047.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_2047.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_2047.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___156_2047.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___156_2047.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___156_2047.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___156_2047.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___156_2047.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___156_2047.FStar_TypeChecker_Env.dsenv)
                     } in
                   let uu____2048 =
                     FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
                   (match uu____2048 with
                    | (ps,w) ->
                        let uu____2061 = FStar_Tactics_Basic.run tau ps in
                        (match uu____2061 with
                         | FStar_Tactics_Result.Success (uu____2070,ps1) ->
                             ((let uu____2073 = FStar_ST.op_Bang tacdbg in
                               if uu____2073
                               then
                                 let uu____2120 =
                                   FStar_Syntax_Print.term_to_string w in
                                 FStar_Util.print1
                                   "Tactic generated proofterm %s\n"
                                   uu____2120
                               else ());
                              FStar_List.iter
                                (fun g  ->
                                   let uu____2127 =
                                     FStar_Tactics_Basic.is_irrelevant g in
                                   if uu____2127
                                   then
                                     let uu____2128 =
                                       FStar_TypeChecker_Rel.teq_nosmt
                                         g.FStar_Tactics_Types.context
                                         g.FStar_Tactics_Types.witness
                                         FStar_Syntax_Util.exp_unit in
                                     (if uu____2128
                                      then ()
                                      else
                                        (let uu____2130 =
                                           let uu____2131 =
                                             FStar_Syntax_Print.term_to_string
                                               g.FStar_Tactics_Types.witness in
                                           FStar_Util.format1
                                             "Irrelevant tactic witness does not unify with (): %s"
                                             uu____2131 in
                                         failwith uu____2130))
                                   else ())
                                (FStar_List.append
                                   ps1.FStar_Tactics_Types.goals
                                   ps1.FStar_Tactics_Types.smt_goals);
                              (let g =
                                 let uu___157_2134 =
                                   FStar_TypeChecker_Rel.trivial_guard in
                                 {
                                   FStar_TypeChecker_Env.guard_f =
                                     (uu___157_2134.FStar_TypeChecker_Env.guard_f);
                                   FStar_TypeChecker_Env.deferred =
                                     (uu___157_2134.FStar_TypeChecker_Env.deferred);
                                   FStar_TypeChecker_Env.univ_ineqs =
                                     (uu___157_2134.FStar_TypeChecker_Env.univ_ineqs);
                                   FStar_TypeChecker_Env.implicits =
                                     (ps1.FStar_Tactics_Types.all_implicits)
                                 } in
                               let g1 =
                                 let uu____2136 =
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env2 g in
                                 FStar_All.pipe_right uu____2136
                                   FStar_TypeChecker_Rel.resolve_implicits_tac in
                               FStar_TypeChecker_Rel.force_trivial_guard env2
                                 g1;
                               ((FStar_List.append
                                   ps1.FStar_Tactics_Types.goals
                                   ps1.FStar_Tactics_Types.smt_goals), w)))
                         | FStar_Tactics_Result.Failed (s,ps1) ->
                             (FStar_Tactics_Basic.dump_proofstate ps1
                                FStar_TypeChecker_Normalize.null_psc
                                "at the time of failure";
                              (let uu____2143 =
                                 let uu____2144 =
                                   let uu____2149 =
                                     FStar_Util.format1
                                       "user tactic failed: %s" s in
                                   (uu____2149,
                                     (typ.FStar_Syntax_Syntax.pos)) in
                                 FStar_Errors.Error uu____2144 in
                               FStar_Exn.raise uu____2143)))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2160 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2165 -> false
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
        let uu____2194 = FStar_Syntax_Util.head_and_args t in
        match uu____2194 with
        | (hd1,args) ->
            let uu____2237 =
              let uu____2250 =
                let uu____2251 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2251.FStar_Syntax_Syntax.n in
              (uu____2250, args) in
            (match uu____2237 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2270))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2339 = run_tactic_on_typ tactic e assertion in
                   (match uu____2339 with
                    | (gs,uu____2353) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2405 =
                     let uu____2408 =
                       let uu____2409 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____2409 in
                     [uu____2408] in
                   (FStar_Syntax_Util.t_true, uu____2405)
                 else (assertion, [])
             | uu____2425 -> (t, []))
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
          let uu____2495 =
            let uu____2502 =
              let uu____2503 = FStar_Syntax_Subst.compress t in
              uu____2503.FStar_Syntax_Syntax.n in
            match uu____2502 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2518 = traverse f pol e t1 in
                (match uu____2518 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____2545 = traverse f pol e t1 in
                (match uu____2545 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2567;
                   FStar_Syntax_Syntax.vars = uu____2568;_},(p,uu____2570)::
                 (q,uu____2572)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2612 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2612 in
                let uu____2613 = traverse f (flip pol) e p in
                (match uu____2613 with
                 | (p',gs1) ->
                     let uu____2632 =
                       let uu____2639 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____2639 q in
                     (match uu____2632 with
                      | (q',gs2) ->
                          let uu____2652 =
                            let uu____2653 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____2653.FStar_Syntax_Syntax.n in
                          (uu____2652, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____2680 = traverse f pol e hd1 in
                (match uu____2680 with
                 | (hd',gs1) ->
                     let uu____2699 =
                       FStar_List.fold_right
                         (fun uu____2737  ->
                            fun uu____2738  ->
                              match (uu____2737, uu____2738) with
                              | ((a,q),(as',gs)) ->
                                  let uu____2819 = traverse f pol e a in
                                  (match uu____2819 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____2699 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2923 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____2923 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____2937 =
                       let uu____2952 =
                         FStar_List.map
                           (fun uu____2985  ->
                              match uu____2985 with
                              | (bv,aq) ->
                                  let uu____3002 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____3002 with
                                   | (s',gs) ->
                                       (((let uu___158_3032 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___158_3032.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___158_3032.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____2952 in
                     (match uu____2937 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____3096 = traverse f pol e' topen in
                          (match uu____3096 with
                           | (topen',gs2) ->
                               let uu____3115 =
                                 let uu____3116 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____3116.FStar_Syntax_Syntax.n in
                               (uu____3115, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2495 with
          | (tn',gs) ->
              let t' =
                let uu___159_3139 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___159_3139.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___159_3139.FStar_Syntax_Syntax.vars)
                } in
              let uu____3140 = f pol e t' in
              (match uu____3140 with
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
      (let uu____3199 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3199);
      (let uu____3247 = FStar_ST.op_Bang tacdbg in
       if uu____3247
       then
         let uu____3294 =
           let uu____3295 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____3295
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____3296 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3294
           uu____3296
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____3325 = traverse by_tactic_interp Pos env goal in
       match uu____3325 with
       | (t',gs) ->
           ((let uu____3347 = FStar_ST.op_Bang tacdbg in
             if uu____3347
             then
               let uu____3394 =
                 let uu____3395 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____3395
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____3396 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3394 uu____3396
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3443  ->
                    fun g  ->
                      match uu____3443 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3488 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____3488 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3491 =
                                  let uu____3492 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____3492 in
                                failwith uu____3491
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____3495 = FStar_ST.op_Bang tacdbg in
                            if uu____3495
                            then
                              let uu____3542 = FStar_Util.string_of_int n1 in
                              let uu____3543 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3542 uu____3543
                            else ());
                           (let gt' =
                              let uu____3546 =
                                let uu____3547 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____3547 in
                              FStar_TypeChecker_Util.label uu____3546
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____3562 = s1 in
             match uu____3562 with
             | (uu____3583,gs1) ->
                 let uu____3601 =
                   let uu____3608 = FStar_Options.peek () in
                   (env, t', uu____3608) in
                 uu____3601 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____3620 =
        let uu____3621 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____3621 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3620 [FStar_Syntax_Syntax.U_zero] in
    let uu____3622 =
      let uu____3623 =
        let uu____3624 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____3625 =
          let uu____3628 = FStar_Syntax_Syntax.as_arg a in [uu____3628] in
        uu____3624 :: uu____3625 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3623 in
    uu____3622 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____3644 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____3644);
        (let uu____3691 =
           let uu____3698 = reify_tactic tau in
           run_tactic_on_typ uu____3698 env typ in
         match uu____3691 with
         | (gs,w) ->
             let uu____3705 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____3709 =
                      let uu____3710 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____3710 in
                    Prims.op_Negation uu____3709) gs in
             if uu____3705
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)