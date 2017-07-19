open Prims
type name = FStar_Syntax_Syntax.bv
let remove_unit f x = f x ()
let quote:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | uu____35::(y,uu____37)::[] ->
          let uu____78 = FStar_Tactics_Embedding.embed_term y in
          FStar_Pervasives_Native.Some uu____78
      | uu____79 -> FStar_Pervasives_Native.None
let binders_of_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (embedded_env,uu____94)::[] ->
            let env =
              FStar_Tactics_Embedding.unembed_env
                ps.FStar_Tactics_Basic.main_context embedded_env in
            let uu____120 =
              let uu____121 = FStar_TypeChecker_Env.all_binders env in
              FStar_Tactics_Embedding.embed_binders uu____121 in
            FStar_Pervasives_Native.Some uu____120
        | uu____124 -> FStar_Pervasives_Native.None
let type_of_binder:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_binder,uu____136)::[] ->
          let uu____161 =
            FStar_Tactics_Embedding.unembed_binder embedded_binder in
          (match uu____161 with
           | (b,uu____165) ->
               let uu____166 =
                 FStar_Tactics_Embedding.embed_term
                   b.FStar_Syntax_Syntax.sort in
               FStar_Pervasives_Native.Some uu____166)
      | uu____167 -> FStar_Pervasives_Native.None
let term_eq:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_t1,uu____179)::(embedded_t2,uu____181)::[] ->
          let t1 = FStar_Tactics_Embedding.unembed_term embedded_t1 in
          let t2 = FStar_Tactics_Embedding.unembed_term embedded_t2 in
          let b = FStar_Syntax_Util.term_eq t1 t2 in
          let uu____225 = FStar_Tactics_Embedding.embed_bool b in
          FStar_Pervasives_Native.Some uu____225
      | uu____226 -> FStar_Pervasives_Native.None
let mk_pure_interpretation_2 f unembed_a unembed_b embed_c nm args =
  (let uu____291 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____291
   then
     let uu____292 = FStar_Ident.string_of_lid nm in
     let uu____293 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____292 uu____293
   else ());
  (match args with
   | (a,uu____298)::(b,uu____300)::[] ->
       let uu____341 =
         let uu____342 =
           let uu____343 = unembed_a a in
           let uu____344 = unembed_b b in f uu____343 uu____344 in
         embed_c uu____342 in
       FStar_Pervasives_Native.Some uu____341
   | uu____345 -> failwith "Unexpected interpretation of pure primitive")
let mk_pure_interpretation_1 f unembed_a embed_b nm args =
  (let uu____395 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____395
   then
     let uu____396 = FStar_Ident.string_of_lid nm in
     let uu____397 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____396 uu____397
   else ());
  (match args with
   | a::[] ->
       let uu____426 =
         let uu____427 =
           let uu____428 = unembed_a (FStar_Pervasives_Native.fst a) in
           f uu____428 in
         embed_b uu____427 in
       FStar_Pervasives_Native.Some uu____426
   | uu____433 -> failwith "Unexpected interpretation of pure primitive")
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____480)::[] ->
      ((let uu____506 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____506
        then
          let uu____507 = FStar_Ident.string_of_lid nm in
          let uu____508 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.print2 "Reached %s, args are: %s\n" uu____507 uu____508
        else ());
       (let uu____510 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____510 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___105_524 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___105_524.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___105_524.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___105_524.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___105_524.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____528 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            FStar_Pervasives_Native.Some uu____528))
  | uu____529 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____593)::(embedded_state,uu____595)::[] ->
      ((let uu____637 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____637
        then
          let uu____638 = FStar_Ident.string_of_lid nm in
          let uu____639 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____638 uu____639
        else ());
       (let uu____641 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____641 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___106_655 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___106_655.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___106_655.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___106_655.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___106_655.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____659 = let uu____662 = unembed_b b in t uu____662 in
              FStar_Tactics_Basic.run uu____659 ps1 in
            let uu____663 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            FStar_Pervasives_Native.Some uu____663))
  | uu____664 ->
      let uu____665 =
        let uu____666 = FStar_Ident.string_of_lid nm in
        let uu____667 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____666 uu____667 in
      failwith uu____665
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____748)::(b,uu____750)::(embedded_state,uu____752)::[] ->
      ((let uu____810 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____810
        then
          let uu____811 = FStar_Ident.string_of_lid nm in
          let uu____812 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____811 uu____812
        else ());
       (let uu____814 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____814 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___107_828 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___107_828.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___107_828.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___107_828.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___107_828.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____832 =
                let uu____835 = unembed_a a in
                let uu____836 = unembed_b b in t uu____835 uu____836 in
              FStar_Tactics_Basic.run uu____832 ps1 in
            let uu____837 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            FStar_Pervasives_Native.Some uu____837))
  | uu____838 ->
      let uu____839 =
        let uu____840 = FStar_Ident.string_of_lid nm in
        let uu____841 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____840 uu____841 in
      failwith uu____839
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____860)::(et2,uu____862)::(embedded_state,uu____864)::[] ->
            let uu____921 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____921 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___108_935 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___108_935.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___108_935.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___108_935.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___108_935.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____939 =
                     let uu____942 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____943 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____944 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____945 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____942 uu____943
                       uu____944 uu____945 in
                   FStar_Tactics_Basic.run uu____939 ps1 in
                 let uu____946 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 FStar_Pervasives_Native.Some uu____946)
        | uu____947 ->
            let uu____948 =
              let uu____949 = FStar_Ident.string_of_lid nm in
              let uu____950 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____949
                uu____950 in
            failwith uu____948
let rec primitive_steps:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  fun ps  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid nm in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      } in
    let uu____1002 =
      mk1 "__forall_intros" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____1003 =
      let uu____1006 =
        mk1 "__implies_intro" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____1007 =
        let uu____1010 =
          mk1 "__trivial" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____1011 =
          let uu____1014 =
            mk1 "__revert" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____1015 =
            let uu____1018 =
              mk1 "__clear" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____1019 =
              let uu____1022 =
                mk1 "__split" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____1023 =
                let uu____1026 =
                  mk1 "__merge" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____1027 =
                  let uu____1030 =
                    mk1 "__rewrite" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____1031 =
                    let uu____1034 =
                      mk1 "__smt" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____1035 =
                      let uu____1038 =
                        mk1 "__exact" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____1039 =
                        let uu____1042 =
                          mk1 "__apply_lemma" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____1043 =
                          let uu____1046 =
                            mk1 "__visit" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____1049 =
                            let uu____1052 =
                              mk1 "__focus" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____1055 =
                              let uu____1058 =
                                mk1 "__seq" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____1063 =
                                let uu____1066 =
                                  mk1 "__term_as_formula"
                                    (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____1069 =
                                  let uu____1072 =
                                    mk1 "__inspect" (Prims.parse_int "1")
                                      (mk_pure_interpretation_1
                                         FStar_Tactics_Embedding.inspect
                                         FStar_Tactics_Embedding.unembed_term
                                         (FStar_Tactics_Embedding.embed_option
                                            FStar_Tactics_Embedding.embed_term_view
                                            FStar_Tactics_Embedding.fstar_tactics_term_view)) in
                                  let uu____1075 =
                                    let uu____1078 =
                                      mk1 "__pack" (Prims.parse_int "1")
                                        (mk_pure_interpretation_1
                                           FStar_Tactics_Embedding.pack
                                           FStar_Tactics_Embedding.unembed_term_view
                                           FStar_Tactics_Embedding.embed_term) in
                                    let uu____1079 =
                                      let uu____1082 =
                                        mk1 "__inspect_fv"
                                          (Prims.parse_int "1")
                                          (mk_pure_interpretation_1
                                             FStar_Tactics_Embedding.inspectfv
                                             FStar_Tactics_Embedding.unembed_fvar
                                             (FStar_Tactics_Embedding.embed_list
                                                FStar_Tactics_Embedding.embed_string
                                                FStar_TypeChecker_Common.t_string)) in
                                      let uu____1085 =
                                        let uu____1088 =
                                          mk1 "__pack_fv"
                                            (Prims.parse_int "1")
                                            (mk_pure_interpretation_1
                                               FStar_Tactics_Embedding.packfv
                                               (FStar_Tactics_Embedding.unembed_list
                                                  FStar_Tactics_Embedding.unembed_string)
                                               FStar_Tactics_Embedding.embed_fvar) in
                                        let uu____1091 =
                                          let uu____1094 =
                                            mk1 "__inspect_bv"
                                              (Prims.parse_int "1")
                                              (mk_pure_interpretation_1
                                                 FStar_Tactics_Embedding.inspectbv
                                                 FStar_Tactics_Embedding.unembed_binder
                                                 FStar_Tactics_Embedding.embed_string) in
                                          let uu____1095 =
                                            let uu____1098 =
                                              mk1 "__compare_binder"
                                                (Prims.parse_int "2")
                                                (mk_pure_interpretation_2
                                                   FStar_Tactics_Basic.order_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.embed_order) in
                                            let uu____1099 =
                                              let uu____1102 =
                                                mk1 "__binders_of_env"
                                                  (Prims.parse_int "1")
                                                  (binders_of_env ps) in
                                              let uu____1103 =
                                                let uu____1106 =
                                                  mk1 "__type_of_binder"
                                                    (Prims.parse_int "1")
                                                    type_of_binder in
                                                let uu____1107 =
                                                  let uu____1110 =
                                                    mk1 "__term_eq"
                                                      (Prims.parse_int "2")
                                                      term_eq in
                                                  let uu____1111 =
                                                    let uu____1114 =
                                                      mk1 "__print"
                                                        (Prims.parse_int "2")
                                                        (mk_tactic_interpretation_1
                                                           ps
                                                           (fun x  ->
                                                              FStar_Tactics_Basic.tacprint
                                                                x;
                                                              FStar_Tactics_Basic.ret
                                                                ())
                                                           FStar_Tactics_Embedding.unembed_string
                                                           FStar_Tactics_Embedding.embed_unit
                                                           FStar_TypeChecker_Common.t_unit) in
                                                    let uu____1117 =
                                                      let uu____1120 =
                                                        mk1 "__dump"
                                                          (Prims.parse_int
                                                             "2")
                                                          (mk_tactic_interpretation_1
                                                             ps
                                                             FStar_Tactics_Basic.print_proof_state
                                                             FStar_Tactics_Embedding.unembed_string
                                                             FStar_Tactics_Embedding.embed_unit
                                                             FStar_TypeChecker_Common.t_unit) in
                                                      let uu____1121 =
                                                        let uu____1124 =
                                                          mk1
                                                            "__term_to_string"
                                                            (Prims.parse_int
                                                               "1")
                                                            (mk_pure_interpretation_1
                                                               FStar_Syntax_Print.term_to_string
                                                               FStar_Tactics_Embedding.unembed_term
                                                               FStar_Tactics_Embedding.embed_string) in
                                                        let uu____1125 =
                                                          let uu____1128 =
                                                            mk1 "__grewrite"
                                                              (Prims.parse_int
                                                                 "3")
                                                              (grewrite_interpretation
                                                                 ps) in
                                                          [uu____1128] in
                                                        uu____1124 ::
                                                          uu____1125 in
                                                      uu____1120 ::
                                                        uu____1121 in
                                                    uu____1114 :: uu____1117 in
                                                  uu____1110 :: uu____1111 in
                                                uu____1106 :: uu____1107 in
                                              uu____1102 :: uu____1103 in
                                            uu____1098 :: uu____1099 in
                                          uu____1094 :: uu____1095 in
                                        uu____1088 :: uu____1091 in
                                      uu____1082 :: uu____1085 in
                                    uu____1078 :: uu____1079 in
                                  uu____1072 :: uu____1075 in
                                uu____1066 :: uu____1069 in
                              uu____1058 :: uu____1063 in
                            uu____1052 :: uu____1055 in
                          uu____1046 :: uu____1049 in
                        uu____1042 :: uu____1043 in
                      uu____1038 :: uu____1039 in
                    uu____1034 :: uu____1035 in
                  uu____1030 :: uu____1031 in
                uu____1026 :: uu____1027 in
              uu____1022 :: uu____1023 in
            uu____1018 :: uu____1019 in
          uu____1014 :: uu____1015 in
        uu____1010 :: uu____1011 in
      uu____1006 :: uu____1007 in
    uu____1002 :: uu____1003
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1139 =
           let uu____1140 =
             let uu____1141 =
               let uu____1142 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____1142 in
             [uu____1141] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1140 in
         uu____1139 FStar_Pervasives_Native.None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1152 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1159  ->
              let uu____1160 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1160) in
       FStar_Tactics_Basic.bind uu____1152
         (fun uu____1161  ->
            let result =
              let uu____1163 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1163 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1166 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1173  ->
                   let uu____1174 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1174) in
            FStar_Tactics_Basic.bind uu____1166
              (fun uu____1175  ->
                 let uu____1176 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____1176 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____1226  ->
                          let uu____1227 =
                            FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____1227
                            (fun uu____1230  ->
                               let uu____1231 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____1231
                                 (fun uu____1234  ->
                                    FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____1270  ->
                          let uu____1271 =
                            FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____1271
                            (fun uu____1274  ->
                               let uu____1275 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____1275
                                 (fun uu____1278  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____1283 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____1283 with
            | (hd1,args) ->
                let uu____1334 =
                  let uu____1349 =
                    let uu____1350 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____1350.FStar_Syntax_Syntax.n in
                  (uu____1349, args) in
                (match uu____1334 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____1369)::(assertion,uu____1371)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____1422 =
                       let uu____1425 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___109_1428 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___109_1428.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___109_1428.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____1425
                         (fun uu____1429  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____1422
                 | uu____1430 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun t  ->
      let uu____1463 = FStar_Syntax_Util.head_and_args t in
      match uu____1463 with
      | (hd1,args) ->
          let uu____1518 =
            let uu____1533 =
              let uu____1534 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1534.FStar_Syntax_Syntax.n in
            (uu____1533, args) in
          (match uu____1518 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____1557)::(assertion,uu____1559)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____1610 =
                 let uu____1613 =
                   unembed_tactic_0 FStar_Tactics_Embedding.unembed_unit
                     tactic in
                 let uu____1616 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____1613 uu____1616 in
               (match uu____1610 with
                | FStar_Tactics_Basic.Success (uu____1623,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____1635 -> (t, []))
let rec traverse:
  (FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term,FStar_Tactics_Basic.goal Prims.list)
         FStar_Pervasives_Native.tuple2)
    ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Tactics_Basic.goal Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun f  ->
    fun e  ->
      fun t  ->
        let uu____1695 =
          let uu____1702 =
            let uu____1703 = FStar_Syntax_Subst.compress t in
            uu____1703.FStar_Syntax_Syntax.n in
          match uu____1702 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1724 = traverse f e t1 in
              (match uu____1724 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1755 = traverse f e t1 in
              (match uu____1755 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1777;
                 FStar_Syntax_Syntax.pos = uu____1778;
                 FStar_Syntax_Syntax.vars = uu____1779;_},(p,uu____1781)::
               (q,uu____1783)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid ->
              let x =
                FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None p in
              let uu____1843 =
                let uu____1850 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1850 q in
              (match uu____1843 with
               | (q',gs) ->
                   let uu____1863 =
                     let uu____1864 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1864.FStar_Syntax_Syntax.n in
                   (uu____1863, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1901 = traverse f e hd1 in
              (match uu____1901 with
               | (hd',gs1) ->
                   let uu____1920 =
                     FStar_List.fold_right
                       (fun uu____1949  ->
                          fun uu____1950  ->
                            match (uu____1949, uu____1950) with
                            | ((a,q),(as',gs)) ->
                                let uu____2031 = traverse f e a in
                                (match uu____2031 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1920 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2159 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2159 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____2173 = traverse f e' topen in
                   (match uu____2173 with
                    | (topen',gs) ->
                        let uu____2192 =
                          let uu____2193 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____2193.FStar_Syntax_Syntax.n in
                        (uu____2192, gs)))
          | x -> (x, []) in
        match uu____1695 with
        | (tn',gs) ->
            let t' =
              let uu___110_2220 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___110_2220.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___110_2220.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___110_2220.FStar_Syntax_Syntax.vars)
              } in
            let uu____2221 = f e t' in
            (match uu____2221 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____2261 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____2261);
      (let uu____2263 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____2263
       then
         let uu____2264 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____2264
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2287 = traverse by_tactic_interp env goal in
       match uu____2287 with
       | (t',gs) ->
           ((let uu____2307 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____2307
             then
               let uu____2308 =
                 let uu____2309 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2309
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2310 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2308 uu____2310
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2344  ->
                    fun g  ->
                      match uu____2344 with
                      | (n1,gs1) ->
                          ((let uu____2381 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____2381
                            then
                              let uu____2382 = FStar_Util.string_of_int n1 in
                              let uu____2383 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2382 uu____2383
                            else ());
                           (let gt' =
                              let uu____2386 =
                                let uu____2387 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____2387 in
                              FStar_TypeChecker_Util.label uu____2386
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____2398 = s1 in
             match uu____2398 with | (uu____2415,gs1) -> (env, t') :: gs1)))