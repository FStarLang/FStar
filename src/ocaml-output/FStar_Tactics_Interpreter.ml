open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let t_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_unit
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____47)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____61  ->
            let uu____62 = FStar_Ident.string_of_lid nm in
            let uu____63 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____62 uu____63);
       (let uu____64 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____64 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___106_73 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___106_73.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___106_73.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___106_73.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____76 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____76))
  | uu____77 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____137)::(embedded_state,uu____139)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____161  ->
            let uu____162 = FStar_Ident.string_of_lid nm in
            let uu____163 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____162
              uu____163);
       (let uu____164 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____164 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___107_173 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___107_173.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___107_173.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___107_173.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____176 = let uu____178 = unembed_b b in t uu____178 in
              FStar_Tactics_Basic.run uu____176 ps1 in
            let uu____179 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____179))
  | uu____180 ->
      let uu____181 =
        let uu____182 = FStar_Ident.string_of_lid nm in
        let uu____183 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____182 uu____183 in
      failwith uu____181
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____260)::(b,uu____262)::(embedded_state,uu____264)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____294  ->
            let uu____295 = FStar_Ident.string_of_lid nm in
            let uu____296 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____295
              uu____296);
       (let uu____297 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____297 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_306 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_306.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_306.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_306.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____309 =
                let uu____311 = unembed_a a in
                let uu____312 = unembed_b b in t uu____311 uu____312 in
              FStar_Tactics_Basic.run uu____309 ps1 in
            let uu____313 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
            Some uu____313))
  | uu____314 ->
      let uu____315 =
        let uu____316 = FStar_Ident.string_of_lid nm in
        let uu____317 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____316 uu____317 in
      failwith uu____315
let mk_tactic_interpretation_3 ps t unembed_a unembed_b unembed_c embed_d t_d
  nm args =
  match args with
  | (a,uu____411)::(b,uu____413)::(c,uu____415)::(embedded_state,uu____417)::[]
      ->
      (FStar_Tactics_Basic.log ps
         (fun uu____455  ->
            let uu____456 = FStar_Ident.string_of_lid nm in
            let uu____457 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____456
              uu____457);
       (let uu____458 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____458 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_467 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_467.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_467.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_467.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____470 =
                let uu____472 = unembed_a a in
                let uu____473 = unembed_b b in
                let uu____474 = unembed_c c in
                t uu____472 uu____473 uu____474 in
              FStar_Tactics_Basic.run uu____470 ps1 in
            let uu____475 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d in
            Some uu____475))
  | uu____476 ->
      let uu____477 =
        let uu____478 = FStar_Ident.string_of_lid nm in
        let uu____479 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____478 uu____479 in
      failwith uu____477
let mk_tactic_interpretation_5 ps t unembed_a unembed_b unembed_c unembed_d
  unembed_e embed_f t_f nm args =
  match args with
  | (a,uu____607)::(b,uu____609)::(c,uu____611)::(d,uu____613)::(e,uu____615)::
      (embedded_state,uu____617)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____671  ->
            let uu____672 = FStar_Ident.string_of_lid nm in
            let uu____673 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____672
              uu____673);
       (let uu____674 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____674 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_683 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_683.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_683.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_683.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____686 =
                let uu____688 = unembed_a a in
                let uu____689 = unembed_b b in
                let uu____690 = unembed_c c in
                let uu____691 = unembed_d d in
                let uu____692 = unembed_e e in
                t uu____688 uu____689 uu____690 uu____691 uu____692 in
              FStar_Tactics_Basic.run uu____686 ps1 in
            let uu____693 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f in
            Some uu____693))
  | uu____694 ->
      let uu____695 =
        let uu____696 = FStar_Ident.string_of_lid nm in
        let uu____697 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____696 uu____697 in
      failwith uu____695
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
      | (e,uu____1124)::[] ->
          let uu____1129 =
            let uu____1130 =
              let uu____1132 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____1132 in
            FStar_Reflection_Basic.embed_binders uu____1130 in
          Some uu____1129
      | uu____1133 ->
          let uu____1137 =
            let uu____1138 = FStar_Ident.string_of_lid nm in
            let uu____1139 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____1138
              uu____1139 in
          failwith uu____1137 in
    let uu____1141 =
      let uu____1143 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1144 =
        let uu____1146 =
          mktac2 "__trytac" (fun uu____1149  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1153 =
          let uu____1155 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1158 =
            let uu____1160 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit in
            let uu____1162 =
              let uu____1164 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1165 =
                let uu____1167 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1168 =
                  let uu____1170 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1171 =
                    let uu____1173 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1174 =
                      let uu____1176 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1177 =
                        let uu____1179 =
                          mktac1 "__exact_lemma"
                            FStar_Tactics_Basic.exact_lemma
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1180 =
                          let uu____1182 =
                            mktac1 "__apply" FStar_Tactics_Basic.apply
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1183 =
                            let uu____1185 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1186 =
                              let uu____1188 =
                                mktac5 "__divide"
                                  (fun uu____1193  ->
                                     fun uu____1194  ->
                                       FStar_Tactics_Basic.divide)
                                  (fun t  -> t) (fun t  -> t)
                                  FStar_Reflection_Basic.unembed_int
                                  (unembed_tactic_0 (fun t  -> t))
                                  (unembed_tactic_0 (fun t  -> t))
                                  (FStar_Reflection_Basic.embed_pair
                                     (fun t  -> t) t_unit (fun t  -> t)
                                     t_unit) t_unit in
                              let uu____1201 =
                                let uu____1203 =
                                  mktac2 "__seq" FStar_Tactics_Basic.seq
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    FStar_Reflection_Basic.embed_unit t_unit in
                                let uu____1206 =
                                  let uu____1208 =
                                    mktac1 "__prune"
                                      FStar_Tactics_Basic.prune
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1209 =
                                    let uu____1211 =
                                      mktac1 "__addns"
                                        FStar_Tactics_Basic.addns
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1212 =
                                      let uu____1214 =
                                        mktac1 "__print"
                                          (fun x  ->
                                             FStar_Tactics_Basic.tacprint x;
                                             FStar_Tactics_Basic.ret ())
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1217 =
                                        let uu____1219 =
                                          mktac1 "__dump"
                                            FStar_Tactics_Basic.print_proof_state
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1220 =
                                          let uu____1222 =
                                            mktac1 "__dump1"
                                              FStar_Tactics_Basic.print_proof_state1
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1223 =
                                            let uu____1225 =
                                              mktac1 "__pointwise"
                                                FStar_Tactics_Basic.pointwise
                                                (unembed_tactic_0
                                                   FStar_Reflection_Basic.unembed_unit)
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1227 =
                                              let uu____1229 =
                                                mktac0 "__trefl"
                                                  FStar_Tactics_Basic.trefl
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1230 =
                                                let uu____1232 =
                                                  mktac0 "__later"
                                                    FStar_Tactics_Basic.later
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1233 =
                                                  let uu____1235 =
                                                    mktac0 "__flip"
                                                      FStar_Tactics_Basic.flip
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1236 =
                                                    let uu____1238 =
                                                      mktac0 "__qed"
                                                        FStar_Tactics_Basic.qed
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1239 =
                                                      let uu____1241 =
                                                        let uu____1242 =
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
                                                          uu____1242 in
                                                      let uu____1245 =
                                                        let uu____1247 =
                                                          mk_refl
                                                            ["Syntax";
                                                            "__binders_of_env"]
                                                            (Prims.parse_int
                                                               "1")
                                                            binders_of_env_int in
                                                        let uu____1248 =
                                                          let uu____1250 =
                                                            mktac0
                                                              "__cur_env"
                                                              FStar_Tactics_Basic.cur_env
                                                              (FStar_Tactics_Embedding.embed_env
                                                                 ps)
                                                              FStar_Reflection_Data.fstar_refl_env in
                                                          let uu____1251 =
                                                            let uu____1253 =
                                                              mktac0
                                                                "__cur_goal"
                                                                FStar_Tactics_Basic.cur_goal'
                                                                FStar_Reflection_Basic.embed_term
                                                                FStar_Reflection_Data.fstar_refl_term in
                                                            let uu____1254 =
                                                              let uu____1256
                                                                =
                                                                mktac0
                                                                  "__cur_witness"
                                                                  FStar_Tactics_Basic.cur_witness
                                                                  FStar_Reflection_Basic.embed_term
                                                                  FStar_Reflection_Data.fstar_refl_term in
                                                              [uu____1256] in
                                                            uu____1253 ::
                                                              uu____1254 in
                                                          uu____1250 ::
                                                            uu____1251 in
                                                        uu____1247 ::
                                                          uu____1248 in
                                                      uu____1241 ::
                                                        uu____1245 in
                                                    uu____1238 :: uu____1239 in
                                                  uu____1235 :: uu____1236 in
                                                uu____1232 :: uu____1233 in
                                              uu____1229 :: uu____1230 in
                                            uu____1225 :: uu____1227 in
                                          uu____1222 :: uu____1223 in
                                        uu____1219 :: uu____1220 in
                                      uu____1214 :: uu____1217 in
                                    uu____1211 :: uu____1212 in
                                  uu____1208 :: uu____1209 in
                                uu____1203 :: uu____1206 in
                              uu____1188 :: uu____1201 in
                            uu____1185 :: uu____1186 in
                          uu____1182 :: uu____1183 in
                        uu____1179 :: uu____1180 in
                      uu____1176 :: uu____1177 in
                    uu____1173 :: uu____1174 in
                  uu____1170 :: uu____1171 in
                uu____1167 :: uu____1168 in
              uu____1164 :: uu____1165 in
            uu____1160 :: uu____1162 in
          uu____1155 :: uu____1158 in
        uu____1146 :: uu____1153 in
      uu____1143 :: uu____1144 in
    FStar_List.append uu____1141
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1265 =
           let uu____1266 =
             let uu____1267 =
               let uu____1268 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals),
                     (proof_state.FStar_Tactics_Basic.smt_goals)) in
               FStar_Syntax_Syntax.as_arg uu____1268 in
             [uu____1267] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1266 in
         uu____1265 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1277 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1282  ->
              let uu____1283 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1283) in
       FStar_Tactics_Basic.bind uu____1277
         (fun uu____1284  ->
            let result =
              let uu____1286 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1286 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1288 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1293  ->
                   let uu____1294 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1294) in
            FStar_Tactics_Basic.bind uu____1288
              (fun uu____1295  ->
                 let uu____1296 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____1296 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____1323  ->
                          let uu____1324 =
                            FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____1324
                            (fun uu____1326  ->
                               let uu____1327 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____1327
                                 (fun uu____1329  ->
                                    FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____1349  ->
                          let uu____1350 =
                            FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____1350
                            (fun uu____1352  ->
                               let uu____1353 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____1353
                                 (fun uu____1355  ->
                                    FStar_Tactics_Basic.fail msg))))))
let run_tactic_on_typ tau env typ =
  let uu____1378 = FStar_TypeChecker_Env.clear_expected_typ env in
  match uu____1378 with
  | (env1,uu____1386) ->
      let env2 =
        let uu___111_1390 = env1 in
        {
          FStar_TypeChecker_Env.solver =
            (uu___111_1390.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___111_1390.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___111_1390.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___111_1390.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___111_1390.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___111_1390.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___111_1390.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___111_1390.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___111_1390.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___111_1390.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___111_1390.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___111_1390.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___111_1390.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___111_1390.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___111_1390.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___111_1390.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___111_1390.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___111_1390.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___111_1390.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___111_1390.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___111_1390.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___111_1390.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___111_1390.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___111_1390.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___111_1390.FStar_TypeChecker_Env.synth)
        } in
      let uu____1391 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
      (match uu____1391 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps) in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1410,ps1) ->
                ((let uu____1413 = FStar_ST.read tacdbg in
                  if uu____1413
                  then
                    let uu____1416 = FStar_Syntax_Print.term_to_string w in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1416
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1420 = FStar_Tactics_Basic.is_irrelevant g in
                      if uu____1420
                      then
                        let uu____1421 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Const.exp_unit in
                        (if uu____1421
                         then ()
                         else
                           (let uu____1423 =
                              let uu____1424 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1424 in
                            failwith uu____1423))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___114_1427 = FStar_TypeChecker_Rel.trivial_guard in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___114_1427.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___114_1427.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___114_1427.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    } in
                  let g1 =
                    let uu____1429 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g in
                    FStar_All.pipe_right uu____1429
                      FStar_TypeChecker_Rel.resolve_implicits_lax in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                let uu____1434 =
                  let uu____1435 =
                    let uu____1438 =
                      FStar_Util.format1 "user tactic failed: %s" s in
                    (uu____1438, (typ.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____1435 in
                raise uu____1434))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1445 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1449 -> false
let flip: pol -> pol = fun p  -> match p with | Pos  -> Neg | Neg  -> Pos
let by_tactic_interp:
  pol ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1468 = FStar_Syntax_Util.head_and_args t in
        match uu____1468 with
        | (hd1,args) ->
            let uu____1497 =
              let uu____1505 =
                let uu____1506 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1506.FStar_Syntax_Syntax.n in
              (uu____1505, args) in
            (match uu____1497 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1519)::(tactic,uu____1521)::(assertion,uu____1523)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1562)::(tactic,uu____1564)::(assertion,uu____1566)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let uu____1600 =
                   let uu____1604 =
                     unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                       tactic in
                   run_tactic_on_typ uu____1604 e assertion in
                 (match uu____1600 with
                  | (gs,uu____1610) -> (FStar_Syntax_Util.t_true, gs))
             | uu____1614 -> (t, []))
let rec traverse:
  (pol ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list))
    ->
    pol ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let uu____1662 =
            let uu____1666 =
              let uu____1667 = FStar_Syntax_Subst.compress t in
              uu____1667.FStar_Syntax_Syntax.n in
            match uu____1666 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1679 = traverse f pol e t1 in
                (match uu____1679 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1697 = traverse f pol e t1 in
                (match uu____1697 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1710;
                   FStar_Syntax_Syntax.pos = uu____1711;
                   FStar_Syntax_Syntax.vars = uu____1712;_},(p,uu____1714)::
                 (q,uu____1716)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p in
                let uu____1747 =
                  let uu____1751 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1751 p in
                (match uu____1747 with
                 | (p',gs1) ->
                     let uu____1759 =
                       let uu____1763 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1763 q in
                     (match uu____1759 with
                      | (q',gs2) ->
                          let uu____1771 =
                            let uu____1772 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1772.FStar_Syntax_Syntax.n in
                          (uu____1771, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1792 = traverse f pol e hd1 in
                (match uu____1792 with
                 | (hd',gs1) ->
                     let uu____1803 =
                       FStar_List.fold_right
                         (fun uu____1818  ->
                            fun uu____1819  ->
                              match (uu____1818, uu____1819) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1862 = traverse f pol e a in
                                  (match uu____1862 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1803 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1930 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1930 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1939 =
                       let uu____1947 =
                         FStar_List.map
                           (fun uu____1961  ->
                              match uu____1961 with
                              | (bv,aq) ->
                                  let uu____1971 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____1971 with
                                   | (s',gs) ->
                                       (((let uu___115_1987 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___115_1987.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___115_1987.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____1947 in
                     (match uu____1939 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____2021 = traverse f pol e' topen in
                          (match uu____2021 with
                           | (topen',gs2) ->
                               let uu____2032 =
                                 let uu____2033 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____2033.FStar_Syntax_Syntax.n in
                               (uu____2032, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____1662 with
          | (tn',gs) ->
              let t' =
                let uu___116_2049 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___116_2049.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___116_2049.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___116_2049.FStar_Syntax_Syntax.vars)
                } in
              let uu____2054 = f pol e t' in
              (match uu____2054 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let getprop:
  FStar_Tactics_Basic.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t in
      let uu____2075 = FStar_Syntax_Util.un_squash tn in
      match uu____2075 with
      | Some t' -> Some t'
      | None  ->
          let uu____2089 = FStar_Syntax_Util.head_and_args tn in
          (match uu____2089 with
           | (hd1,uu____2101) ->
               let uu____2116 =
                 let uu____2117 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____2117.FStar_Syntax_Syntax.n in
               (match uu____2116 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid
                    -> Some t
                | uu____2122 -> None))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____2136 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____2136);
      (let uu____2140 = FStar_ST.read tacdbg in
       if uu____2140
       then
         let uu____2143 =
           let uu____2144 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2144
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2145 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2143
           uu____2145
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2158 = traverse by_tactic_interp Pos env goal in
       match uu____2158 with
       | (t',gs) ->
           ((let uu____2170 = FStar_ST.read tacdbg in
             if uu____2170
             then
               let uu____2173 =
                 let uu____2174 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2174
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2175 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2173 uu____2175
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2194  ->
                    fun g  ->
                      match uu____2194 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2215 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty in
                            match uu____2215 with
                            | None  ->
                                let uu____2217 =
                                  let uu____2218 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2218 in
                                failwith uu____2217
                            | Some phi -> phi in
                          ((let uu____2221 = FStar_ST.read tacdbg in
                            if uu____2221
                            then
                              let uu____2224 = FStar_Util.string_of_int n1 in
                              let uu____2225 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2224 uu____2225
                            else ());
                           (let gt' =
                              let uu____2228 =
                                let uu____2229 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____2229 in
                              FStar_TypeChecker_Util.label uu____2228
                                FStar_Range.dummyRange phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____2235 = s1 in
             match uu____2235 with | (uu____2244,gs1) -> (env, t') :: gs1)))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____2258 =
        let uu____2259 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational None in
        FStar_Syntax_Syntax.fv_to_tm uu____2259 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____2258 [FStar_Syntax_Syntax.U_zero] in
    let uu____2260 =
      let uu____2261 =
        let uu____2262 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____2263 =
          let uu____2265 = FStar_Syntax_Syntax.as_arg a in [uu____2265] in
        uu____2262 :: uu____2263 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____2261 in
    uu____2260 None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____2279 =
          let uu____2283 =
            let uu____2285 = reify_tactic tau in
            unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____2285 in
          run_tactic_on_typ uu____2283 env typ in
        match uu____2279 with
        | (gs,w) ->
            (match gs with
             | [] -> w
             | uu____2290::uu____2291 ->
                 raise
                   (FStar_Errors.Error
                      ("synthesis left open goals",
                        (typ.FStar_Syntax_Syntax.pos))))