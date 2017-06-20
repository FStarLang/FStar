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
         (fun uu____68  ->
            let uu____69 = FStar_Ident.string_of_lid nm in
            let uu____70 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____69 uu____70);
       (let uu____71 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____71 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_80 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_80.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_80.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_80.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____83 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____83))
  | uu____84 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____144)::(embedded_state,uu____146)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____177  ->
            let uu____178 = FStar_Ident.string_of_lid nm in
            let uu____179 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____178
              uu____179);
       (let uu____180 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____180 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_189 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_189.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_189.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_189.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____192 = let uu____194 = unembed_b b in t uu____194 in
              FStar_Tactics_Basic.run uu____192 ps1 in
            let uu____195 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____195))
  | uu____196 ->
      let uu____197 =
        let uu____198 = FStar_Ident.string_of_lid nm in
        let uu____199 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____180 uu____181 in
      failwith uu____179
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____269)::(b,uu____271)::(embedded_state,uu____273)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____321  ->
            let uu____322 = FStar_Ident.string_of_lid nm in
            let uu____323 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____322
              uu____323);
       (let uu____324 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____324 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___111_333 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___111_333.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___111_333.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___111_333.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____336 =
                let uu____338 = unembed_a a in
                let uu____339 = unembed_b b in t uu____338 uu____339 in
              FStar_Tactics_Basic.run uu____336 ps1 in
            let uu____340 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
            Some uu____340))
  | uu____341 ->
      let uu____342 =
        let uu____343 = FStar_Ident.string_of_lid nm in
        let uu____344 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____316 uu____317 in
      failwith uu____315
let mk_tactic_interpretation_3 ps t unembed_a unembed_b unembed_c embed_d t_d
  nm args =
  match args with
  | (a,uu____424)::(b,uu____426)::(c,uu____428)::(embedded_state,uu____430)::[]
      ->
      (FStar_Tactics_Basic.log ps
         (fun uu____468  ->
            let uu____469 = FStar_Ident.string_of_lid nm in
            let uu____470 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____469
              uu____470);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____474 =
            let uu____476 = unembed_a a in
            let uu____477 = unembed_b b in
            let uu____478 = unembed_c c in t uu____476 uu____477 uu____478 in
          FStar_Tactics_Basic.run uu____474 ps1 in
        let uu____479 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d in
        Some uu____479))
  | uu____480 ->
      let uu____481 =
        let uu____482 = FStar_Ident.string_of_lid nm in
        let uu____483 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____482 uu____483 in
      failwith uu____481
let mk_tactic_interpretation_5 ps t unembed_a unembed_b unembed_c unembed_d
  unembed_e embed_f t_f nm args =
  match args with
  | (a,uu____628)::(b,uu____630)::(c,uu____632)::(d,uu____634)::(e,uu____636)::
      (embedded_state,uu____638)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____692  ->
            let uu____693 = FStar_Ident.string_of_lid nm in
            let uu____694 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____693
              uu____694);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____698 =
            let uu____700 = unembed_a a in
            let uu____701 = unembed_b b in
            let uu____702 = unembed_c c in
            let uu____703 = unembed_d d in
            let uu____704 = unembed_e e in
            t uu____700 uu____701 uu____702 uu____703 uu____704 in
          FStar_Tactics_Basic.run uu____698 ps1 in
        let uu____705 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f in
        Some uu____705))
  | uu____706 ->
      let uu____707 =
        let uu____708 = FStar_Ident.string_of_lid nm in
        let uu____709 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____708 uu____709 in
      failwith uu____707
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____720 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____720);
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
      | (e,uu____1156)::[] ->
          let uu____1161 =
            let uu____1162 =
              let uu____1164 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____1164 in
            FStar_Reflection_Basic.embed_binders uu____1162 in
          Some uu____1161
      | uu____1165 ->
          let uu____1169 =
            let uu____1170 = FStar_Ident.string_of_lid nm in
            let uu____1171 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____1170
              uu____1171 in
          failwith uu____1169 in
    let uu____1173 =
      let uu____1175 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1176 =
        let uu____1178 =
          mktac2 "__trytac" (fun uu____1181  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1185 =
          let uu____1187 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1190 =
            let uu____1192 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit in
            let uu____1194 =
              let uu____1196 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1197 =
                let uu____1199 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1200 =
                  let uu____1202 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1203 =
                    let uu____1205 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1206 =
                      let uu____1208 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1209 =
                        let uu____1211 =
                          mktac1 "__exact_lemma"
                            FStar_Tactics_Basic.exact_lemma
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1212 =
                          let uu____1214 =
                            mktac1 "__apply" FStar_Tactics_Basic.apply
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1215 =
                            let uu____1217 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1218 =
                              let uu____1220 =
                                mktac5 "__divide"
                                  (fun uu____1225  ->
                                     fun uu____1226  ->
                                       FStar_Tactics_Basic.divide)
                                  (fun t  -> t) (fun t  -> t)
                                  FStar_Reflection_Basic.unembed_int
                                  (unembed_tactic_0 (fun t  -> t))
                                  (unembed_tactic_0 (fun t  -> t))
                                  (FStar_Reflection_Basic.embed_pair
                                     (fun t  -> t) t_unit (fun t  -> t)
                                     t_unit) t_unit in
                              let uu____1233 =
                                let uu____1235 =
                                  mktac1 "__set_options"
                                    FStar_Tactics_Basic.set_options
                                    FStar_Reflection_Basic.unembed_string
                                    FStar_Reflection_Basic.embed_unit t_unit in
                                let uu____1236 =
                                  let uu____1238 =
                                    mktac2 "__seq" FStar_Tactics_Basic.seq
                                      (unembed_tactic_0
                                         FStar_Reflection_Basic.unembed_unit)
                                      (unembed_tactic_0
                                         FStar_Reflection_Basic.unembed_unit)
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1241 =
                                    let uu____1243 =
                                      mktac1 "__prune"
                                        FStar_Tactics_Basic.prune
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1244 =
                                      let uu____1246 =
                                        mktac1 "__addns"
                                          FStar_Tactics_Basic.addns
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1247 =
                                        let uu____1249 =
                                          mktac1 "__print"
                                            (fun x  ->
                                               FStar_Tactics_Basic.tacprint x;
                                               FStar_Tactics_Basic.ret ())
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1252 =
                                          let uu____1254 =
                                            mktac1 "__dump"
                                              FStar_Tactics_Basic.print_proof_state
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1255 =
                                            let uu____1257 =
                                              mktac1 "__dump1"
                                                FStar_Tactics_Basic.print_proof_state1
                                                FStar_Reflection_Basic.unembed_string
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1258 =
                                              let uu____1260 =
                                                mktac1 "__pointwise"
                                                  FStar_Tactics_Basic.pointwise
                                                  (unembed_tactic_0
                                                     FStar_Reflection_Basic.unembed_unit)
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1262 =
                                                let uu____1264 =
                                                  mktac0 "__trefl"
                                                    FStar_Tactics_Basic.trefl
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1265 =
                                                  let uu____1267 =
                                                    mktac0 "__later"
                                                      FStar_Tactics_Basic.later
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1268 =
                                                    let uu____1270 =
                                                      mktac0 "__flip"
                                                        FStar_Tactics_Basic.flip
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1271 =
                                                      let uu____1273 =
                                                        mktac0 "__qed"
                                                          FStar_Tactics_Basic.qed
                                                          FStar_Reflection_Basic.embed_unit
                                                          t_unit in
                                                      let uu____1274 =
                                                        let uu____1276 =
                                                          let uu____1277 =
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
                                                            uu____1277 in
                                                        let uu____1280 =
                                                          let uu____1282 =
                                                            mk_refl
                                                              ["Syntax";
                                                              "__binders_of_env"]
                                                              (Prims.parse_int
                                                                 "1")
                                                              binders_of_env_int in
                                                          let uu____1283 =
                                                            let uu____1285 =
                                                              mktac0
                                                                "__cur_env"
                                                                FStar_Tactics_Basic.cur_env
                                                                (FStar_Tactics_Embedding.embed_env
                                                                   ps)
                                                                FStar_Reflection_Data.fstar_refl_env in
                                                            let uu____1286 =
                                                              let uu____1288
                                                                =
                                                                mktac0
                                                                  "__cur_goal"
                                                                  FStar_Tactics_Basic.cur_goal'
                                                                  FStar_Reflection_Basic.embed_term
                                                                  FStar_Reflection_Data.fstar_refl_term in
                                                              let uu____1289
                                                                =
                                                                let uu____1291
                                                                  =
                                                                  mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term in
                                                                [uu____1291] in
                                                              uu____1288 ::
                                                                uu____1289 in
                                                            uu____1285 ::
                                                              uu____1286 in
                                                          uu____1282 ::
                                                            uu____1283 in
                                                        uu____1276 ::
                                                          uu____1280 in
                                                      uu____1273 ::
                                                        uu____1274 in
                                                    uu____1270 :: uu____1271 in
                                                  uu____1267 :: uu____1268 in
                                                uu____1264 :: uu____1265 in
                                              uu____1260 :: uu____1262 in
                                            uu____1257 :: uu____1258 in
                                          uu____1254 :: uu____1255 in
                                        uu____1249 :: uu____1252 in
                                      uu____1246 :: uu____1247 in
                                    uu____1243 :: uu____1244 in
                                  uu____1238 :: uu____1241 in
                                uu____1235 :: uu____1236 in
                              uu____1220 :: uu____1233 in
                            uu____1217 :: uu____1218 in
                          uu____1214 :: uu____1215 in
                        uu____1211 :: uu____1212 in
                      uu____1208 :: uu____1209 in
                    uu____1205 :: uu____1206 in
                  uu____1202 :: uu____1203 in
                uu____1199 :: uu____1200 in
              uu____1196 :: uu____1197 in
            uu____1192 :: uu____1194 in
          uu____1187 :: uu____1190 in
        uu____1178 :: uu____1185 in
      uu____1175 :: uu____1176 in
    FStar_List.append uu____1173
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1300 =
           let uu____1301 =
             let uu____1302 =
               let uu____1303 =
                 FStar_Tactics_Embedding.embed_proofstate proof_state in
               FStar_Syntax_Syntax.as_arg uu____1303 in
             [uu____1302] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1301 in
         uu____1300 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1310 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1315  ->
              let uu____1316 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1316) in
       FStar_Tactics_Basic.bind uu____1310
         (fun uu____1317  ->
            let result =
              let uu____1319 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1319 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1321 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1326  ->
                   let uu____1327 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1327) in
            FStar_Tactics_Basic.bind uu____1321
              (fun uu____1328  ->
                 let uu____1329 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____1329 with
                 | FStar_Util.Inl (b,ps) ->
                     let uu____1343 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1343
                       (fun uu____1345  -> FStar_Tactics_Basic.ret b)
                 | FStar_Util.Inr (msg,ps) ->
                     let uu____1352 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1352
                       (fun uu____1354  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ tau env typ =
  let uu____1381 = FStar_TypeChecker_Env.clear_expected_typ env in
  match uu____1381 with
  | (env1,uu____1389) ->
      let env2 =
        let uu___107_1393 = env1 in
        {
          FStar_TypeChecker_Env.solver =
            (uu___107_1393.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___107_1393.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___107_1393.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___107_1393.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___107_1393.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___107_1393.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___107_1393.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___107_1393.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___107_1393.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___107_1393.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___107_1393.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___107_1393.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___107_1393.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___107_1393.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___107_1393.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___107_1393.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___107_1393.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___107_1393.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___107_1393.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___107_1393.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___107_1393.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___107_1393.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___107_1393.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___107_1393.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___107_1393.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___107_1393.FStar_TypeChecker_Env.is_native_tactic)
        } in
      let uu____1394 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
      (match uu____1394 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps) in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1413,ps1) ->
                ((let uu____1416 = FStar_ST.read tacdbg in
                  if uu____1416
                  then
                    let uu____1419 = FStar_Syntax_Print.term_to_string w in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1419
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1423 = FStar_Tactics_Basic.is_irrelevant g in
                      if uu____1423
                      then
                        let uu____1424 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Const.exp_unit in
                        (if uu____1424
                         then ()
                         else
                           (let uu____1426 =
                              let uu____1427 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1427 in
                            failwith uu____1426))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___110_1430 = FStar_TypeChecker_Rel.trivial_guard in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___110_1430.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___110_1430.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___110_1430.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    } in
                  let g1 =
                    let uu____1432 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g in
                    FStar_All.pipe_right uu____1432
                      FStar_TypeChecker_Rel.resolve_implicits_lax in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                let uu____1437 =
                  let uu____1438 =
                    let uu____1441 =
                      FStar_Util.format1 "user tactic failed: %s" s in
                    (uu____1441, (typ.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____1438 in
                raise uu____1437))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1449 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1454 -> false
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
        let uu____1477 = FStar_Syntax_Util.head_and_args t in
        match uu____1477 with
        | (hd1,args) ->
            let uu____1506 =
              let uu____1514 =
                let uu____1515 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1515.FStar_Syntax_Syntax.n in
              (uu____1514, args) in
            (match uu____1506 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1528)::(tactic,uu____1530)::(assertion,uu____1532)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1571)::(tactic,uu____1573)::(assertion,uu____1575)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let uu____1609 =
                   let uu____1613 =
                     unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                       tactic in
                   run_tactic_on_typ uu____1613 e assertion in
                 (match uu____1609 with
                  | (gs,uu____1619) -> (FStar_Syntax_Util.t_true, gs))
             | uu____1623 -> (t, []))
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
          let uu____1675 =
            let uu____1679 =
              let uu____1680 = FStar_Syntax_Subst.compress t in
              uu____1680.FStar_Syntax_Syntax.n in
            match uu____1679 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1692 = traverse f pol e t1 in
                (match uu____1692 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1710 = traverse f pol e t1 in
                (match uu____1710 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1723;
                   FStar_Syntax_Syntax.pos = uu____1724;
                   FStar_Syntax_Syntax.vars = uu____1725;_},(p,uu____1727)::
                 (q,uu____1729)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p in
                let uu____1760 =
                  let uu____1764 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1764 p in
                (match uu____1760 with
                 | (p',gs1) ->
                     let uu____1772 =
                       let uu____1776 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1776 q in
                     (match uu____1772 with
                      | (q',gs2) ->
                          let uu____1784 =
                            let uu____1785 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1785.FStar_Syntax_Syntax.n in
                          (uu____1784, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1805 = traverse f pol e hd1 in
                (match uu____1805 with
                 | (hd',gs1) ->
                     let uu____1816 =
                       FStar_List.fold_right
                         (fun uu____1831  ->
                            fun uu____1832  ->
                              match (uu____1831, uu____1832) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1875 = traverse f pol e a in
                                  (match uu____1875 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1816 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1326 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1326 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1335 =
                       let uu____1343 =
                         FStar_List.map
                           (fun uu____1357  ->
                              match uu____1357 with
                              | (bv,aq) ->
                                  let uu____1367 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____1367 with
                                   | (s',gs) ->
                                       (((let uu___114_1383 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___114_1383.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___114_1383.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____1343 in
                     (match uu____1335 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____1417 = traverse f pol e' topen in
                          (match uu____1417 with
                           | (topen',gs2) ->
                               let uu____1428 =
                                 let uu____1429 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____1429.FStar_Syntax_Syntax.n in
                               (uu____1428, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____1675 with
          | (tn',gs) ->
              let t' =
                let uu___115_1445 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___115_1445.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___115_1445.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___115_1445.FStar_Syntax_Syntax.vars)
                } in
              let uu____1450 = f pol e t' in
              (match uu____1450 with
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
      let uu____1473 = FStar_Syntax_Util.un_squash tn in
      match uu____1473 with
      | Some t' -> Some t'
      | None  ->
          let uu____1487 = FStar_Syntax_Util.head_and_args tn in
          (match uu____1487 with
           | (hd1,uu____1499) ->
               let uu____1514 =
                 let uu____1515 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____1515.FStar_Syntax_Syntax.n in
               (match uu____1514 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid
                    -> Some t
                | uu____1520 -> None))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term*
        FStar_Options.optionstate) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1536 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1536);
      (let uu____1540 = FStar_ST.read tacdbg in
       if uu____1540
       then
         let uu____1543 =
           let uu____1544 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____1544
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____1545 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____1543
           uu____1545
       else ());
      (let uu____1547 = FStar_TypeChecker_Env.clear_expected_typ env in
       match uu____1547 with
       | (env1,uu____1555) ->
           let env2 =
             let uu___116_1559 = env1 in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___116_1559.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___116_1559.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___116_1559.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___116_1559.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___116_1559.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___116_1559.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___116_1559.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___116_1559.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___116_1559.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp = false;
               FStar_TypeChecker_Env.effects =
                 (uu___116_1559.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___116_1559.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___116_1559.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___116_1559.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___116_1559.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___116_1559.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___116_1559.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___116_1559.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___116_1559.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___116_1559.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.type_of =
                 (uu___116_1559.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___116_1559.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___116_1559.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___116_1559.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___116_1559.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___116_1559.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___116_1559.FStar_TypeChecker_Env.is_native_tactic)
             } in
           let initial = ((Prims.parse_int "1"), []) in
           let uu____1571 = traverse by_tactic_interp Pos env2 goal in
           (match uu____1571 with
            | (t',gs) ->
                ((let uu____1583 = FStar_ST.read tacdbg in
                  if uu____1583
                  then
                    let uu____1586 =
                      let uu____1587 = FStar_TypeChecker_Env.all_binders env2 in
                      FStar_All.pipe_right uu____1587
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu____1588 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                      uu____1586 uu____1588
                  else ());
                 (let s = initial in
                  let s1 =
                    FStar_List.fold_left
                      (fun uu____1607  ->
                         fun g  ->
                           match uu____1607 with
                           | (n1,gs1) ->
                               let phi =
                                 let uu____1628 =
                                   getprop g.FStar_Tactics_Basic.context
                                     g.FStar_Tactics_Basic.goal_ty in
                                 match uu____1628 with
                                 | None  ->
                                     let uu____1630 =
                                       let uu____1631 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Basic.goal_ty in
                                       FStar_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu____1631 in
                                     failwith uu____1630
                                 | Some phi -> phi in
                               ((let uu____1634 =
                                   let uu____1635 =
                                     FStar_TypeChecker_Rel.teq_nosmt
                                       g.FStar_Tactics_Basic.context
                                       g.FStar_Tactics_Basic.witness
                                       FStar_Syntax_Const.exp_unit in
                                   Prims.op_Negation uu____1635 in
                                 if uu____1634
                                 then
                                   let uu____1636 =
                                     let uu____1637 =
                                       FStar_Syntax_Print.term_to_string
                                         g.FStar_Tactics_Basic.witness in
                                     FStar_Util.format1
                                       "Irrelevant tactic witness does not unify with (): %s"
                                       uu____1637 in
                                   failwith uu____1636
                                 else
                                   (let uu____1639 = FStar_ST.read tacdbg in
                                    if uu____1639
                                    then
                                      let uu____1642 =
                                        FStar_Util.string_of_int n1 in
                                      let uu____1643 =
                                        FStar_Tactics_Basic.goal_to_string g in
                                      FStar_Util.print2 "Got goal #%s: %s\n"
                                        uu____1642 uu____1643
                                    else ()));
                                (let gt' =
                                   let uu____1646 =
                                     let uu____1647 =
                                       FStar_Util.string_of_int n1 in
                                     Prims.strcat "Could not prove goal #"
                                       uu____1647 in
                                   FStar_TypeChecker_Util.label uu____1646
                                     FStar_Range.dummyRange phi in
                                 ((n1 + (Prims.parse_int "1")),
                                   (((g.FStar_Tactics_Basic.context), gt') ::
                                   gs1))))) s gs in
                  let uu____1653 = s1 in
                  match uu____1653 with
                  | (uu____1662,gs1) -> (env2, t') :: gs1))))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____1677 =
        let uu____1678 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational None in
        FStar_Syntax_Syntax.fv_to_tm uu____1678 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____1677 [FStar_Syntax_Syntax.U_zero] in
    let uu____1679 =
      let uu____1680 =
        let uu____1681 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____1682 =
          let uu____1684 = FStar_Syntax_Syntax.as_arg a in [uu____1684] in
        uu____1681 :: uu____1682 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____1680 in
    uu____1679 None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let ps = FStar_Tactics_Basic.proofstate_of_goal_ty env typ in
        let w =
          let uu____1703 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
          uu____1703.FStar_Tactics_Basic.witness in
        let r =
          try
            let uu____1709 =
              let uu____1711 = reify_tactic tau in
              unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____1711 in
            FStar_Tactics_Basic.run uu____1709 ps
          with
          | FStar_Tactics_Basic.TacFailure s ->
              FStar_Tactics_Basic.Failed ((Prims.strcat "EXCEPTION: " s), ps) in
        match r with
        | FStar_Tactics_Basic.Success (uu____1715,ps1) ->
            ((let uu____1718 = FStar_ST.read tacdbg in
              if uu____1718
              then
                let uu____1721 = FStar_Syntax_Print.term_to_string w in
                FStar_Util.print1 "Tactic generated proofterm %s\n"
                  uu____1721
              else ());
             w)
        | FStar_Tactics_Basic.Failed (s,ps1) ->
            ((let uu____1726 = FStar_Util.format1 "user tactic failed: %s" s in
              FStar_Errors.err typ.FStar_Syntax_Syntax.pos uu____1726);
             failwith "aborting")