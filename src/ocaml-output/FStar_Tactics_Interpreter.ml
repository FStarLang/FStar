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
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res = FStar_Tactics_Basic.run t ps1 in
        let uu____67 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        Some uu____67))
  | uu____68 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____128)::(embedded_state,uu____130)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____152  ->
            let uu____153 = FStar_Ident.string_of_lid nm in
            let uu____154 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____153
              uu____154);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____158 = let uu____160 = unembed_b b in t uu____160 in
          FStar_Tactics_Basic.run uu____158 ps1 in
        let uu____161 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
        Some uu____161))
  | uu____162 ->
      let uu____163 =
        let uu____164 = FStar_Ident.string_of_lid nm in
        let uu____165 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____164 uu____165 in
      failwith uu____163
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____242)::(b,uu____244)::(embedded_state,uu____246)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____276  ->
            let uu____277 = FStar_Ident.string_of_lid nm in
            let uu____278 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____277
              uu____278);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____282 =
            let uu____284 = unembed_a a in
            let uu____285 = unembed_b b in t uu____284 uu____285 in
          FStar_Tactics_Basic.run uu____282 ps1 in
        let uu____286 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
        Some uu____286))
  | uu____287 ->
      let uu____288 =
        let uu____289 = FStar_Ident.string_of_lid nm in
        let uu____290 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____289 uu____290 in
      failwith uu____288
let mk_tactic_interpretation_3 ps t unembed_a unembed_b unembed_c embed_d t_d
  nm args =
  match args with
  | (a,uu____384)::(b,uu____386)::(c,uu____388)::(embedded_state,uu____390)::[]
      ->
      (FStar_Tactics_Basic.log ps
         (fun uu____428  ->
            let uu____429 = FStar_Ident.string_of_lid nm in
            let uu____430 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____429
              uu____430);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____434 =
            let uu____436 = unembed_a a in
            let uu____437 = unembed_b b in
            let uu____438 = unembed_c c in t uu____436 uu____437 uu____438 in
          FStar_Tactics_Basic.run uu____434 ps1 in
        let uu____439 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d in
        Some uu____439))
  | uu____440 ->
      let uu____441 =
        let uu____442 = FStar_Ident.string_of_lid nm in
        let uu____443 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____442 uu____443 in
      failwith uu____441
let mk_tactic_interpretation_5 ps t unembed_a unembed_b unembed_c unembed_d
  unembed_e embed_f t_f nm args =
  match args with
  | (a,uu____571)::(b,uu____573)::(c,uu____575)::(d,uu____577)::(e,uu____579)::
      (embedded_state,uu____581)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____635  ->
            let uu____636 = FStar_Ident.string_of_lid nm in
            let uu____637 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____636
              uu____637);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state in
        let res =
          let uu____641 =
            let uu____643 = unembed_a a in
            let uu____644 = unembed_b b in
            let uu____645 = unembed_c c in
            let uu____646 = unembed_d d in
            let uu____647 = unembed_e e in
            t uu____643 uu____644 uu____645 uu____646 uu____647 in
          FStar_Tactics_Basic.run uu____641 ps1 in
        let uu____648 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f in
        Some uu____648))
  | uu____649 ->
      let uu____650 =
        let uu____651 = FStar_Ident.string_of_lid nm in
        let uu____652 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____651 uu____652 in
      failwith uu____650
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
      | (e,uu____1079)::[] ->
          let uu____1084 =
            let uu____1085 =
              let uu____1087 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____1087 in
            FStar_Reflection_Basic.embed_binders uu____1085 in
          Some uu____1084
      | uu____1088 ->
          let uu____1092 =
            let uu____1093 = FStar_Ident.string_of_lid nm in
            let uu____1094 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____1093
              uu____1094 in
          failwith uu____1092 in
    let uu____1096 =
      let uu____1098 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____1099 =
        let uu____1101 =
          mktac2 "__trytac" (fun uu____1104  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____1108 =
          let uu____1110 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1113 =
            let uu____1115 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit in
            let uu____1117 =
              let uu____1119 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____1120 =
                let uu____1122 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____1123 =
                  let uu____1125 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____1126 =
                    let uu____1128 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____1129 =
                      let uu____1131 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____1132 =
                        let uu____1134 =
                          mktac1 "__exact_lemma"
                            FStar_Tactics_Basic.exact_lemma
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____1135 =
                          let uu____1137 =
                            mktac1 "__apply" FStar_Tactics_Basic.apply
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____1138 =
                            let uu____1140 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____1141 =
                              let uu____1143 =
                                mktac5 "__divide"
                                  (fun uu____1148  ->
                                     fun uu____1149  ->
                                       FStar_Tactics_Basic.divide)
                                  (fun t  -> t) (fun t  -> t)
                                  FStar_Reflection_Basic.unembed_int
                                  (unembed_tactic_0 (fun t  -> t))
                                  (unembed_tactic_0 (fun t  -> t))
                                  (FStar_Reflection_Basic.embed_pair
                                     (fun t  -> t) t_unit (fun t  -> t)
                                     t_unit) t_unit in
                              let uu____1156 =
                                let uu____1158 =
                                  mktac2 "__seq" FStar_Tactics_Basic.seq
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    FStar_Reflection_Basic.embed_unit t_unit in
                                let uu____1161 =
                                  let uu____1163 =
                                    mktac1 "__prune"
                                      FStar_Tactics_Basic.prune
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____1164 =
                                    let uu____1166 =
                                      mktac1 "__addns"
                                        FStar_Tactics_Basic.addns
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____1167 =
                                      let uu____1169 =
                                        mktac1 "__print"
                                          (fun x  ->
                                             FStar_Tactics_Basic.tacprint x;
                                             FStar_Tactics_Basic.ret ())
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____1172 =
                                        let uu____1174 =
                                          mktac1 "__dump"
                                            FStar_Tactics_Basic.print_proof_state
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____1175 =
                                          let uu____1177 =
                                            mktac1 "__dump1"
                                              FStar_Tactics_Basic.print_proof_state1
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____1178 =
                                            let uu____1180 =
                                              mktac1 "__pointwise"
                                                FStar_Tactics_Basic.pointwise
                                                (unembed_tactic_0
                                                   FStar_Reflection_Basic.unembed_unit)
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____1182 =
                                              let uu____1184 =
                                                mktac0 "__trefl"
                                                  FStar_Tactics_Basic.trefl
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____1185 =
                                                let uu____1187 =
                                                  mktac0 "__later"
                                                    FStar_Tactics_Basic.later
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____1188 =
                                                  let uu____1190 =
                                                    mktac0 "__flip"
                                                      FStar_Tactics_Basic.flip
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____1191 =
                                                    let uu____1193 =
                                                      mktac0 "__qed"
                                                        FStar_Tactics_Basic.qed
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____1194 =
                                                      let uu____1196 =
                                                        let uu____1197 =
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
                                                          uu____1197 in
                                                      let uu____1200 =
                                                        let uu____1202 =
                                                          mk_refl
                                                            ["Syntax";
                                                            "__binders_of_env"]
                                                            (Prims.parse_int
                                                               "1")
                                                            binders_of_env_int in
                                                        let uu____1203 =
                                                          let uu____1205 =
                                                            mktac0
                                                              "__cur_env"
                                                              FStar_Tactics_Basic.cur_env
                                                              (FStar_Tactics_Embedding.embed_env
                                                                 ps)
                                                              FStar_Reflection_Data.fstar_refl_env in
                                                          let uu____1206 =
                                                            let uu____1208 =
                                                              mktac0
                                                                "__cur_goal"
                                                                FStar_Tactics_Basic.cur_goal'
                                                                FStar_Reflection_Basic.embed_term
                                                                FStar_Reflection_Data.fstar_refl_term in
                                                            let uu____1209 =
                                                              let uu____1211
                                                                =
                                                                mktac0
                                                                  "__cur_witness"
                                                                  FStar_Tactics_Basic.cur_witness
                                                                  FStar_Reflection_Basic.embed_term
                                                                  FStar_Reflection_Data.fstar_refl_term in
                                                              [uu____1211] in
                                                            uu____1208 ::
                                                              uu____1209 in
                                                          uu____1205 ::
                                                            uu____1206 in
                                                        uu____1202 ::
                                                          uu____1203 in
                                                      uu____1196 ::
                                                        uu____1200 in
                                                    uu____1193 :: uu____1194 in
                                                  uu____1190 :: uu____1191 in
                                                uu____1187 :: uu____1188 in
                                              uu____1184 :: uu____1185 in
                                            uu____1180 :: uu____1182 in
                                          uu____1177 :: uu____1178 in
                                        uu____1174 :: uu____1175 in
                                      uu____1169 :: uu____1172 in
                                    uu____1166 :: uu____1167 in
                                  uu____1163 :: uu____1164 in
                                uu____1158 :: uu____1161 in
                              uu____1143 :: uu____1156 in
                            uu____1140 :: uu____1141 in
                          uu____1137 :: uu____1138 in
                        uu____1134 :: uu____1135 in
                      uu____1131 :: uu____1132 in
                    uu____1128 :: uu____1129 in
                  uu____1125 :: uu____1126 in
                uu____1122 :: uu____1123 in
              uu____1119 :: uu____1120 in
            uu____1115 :: uu____1117 in
          uu____1110 :: uu____1113 in
        uu____1101 :: uu____1108 in
      uu____1098 :: uu____1099 in
    FStar_List.append uu____1096
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1220 =
           let uu____1221 =
             let uu____1222 =
               let uu____1223 =
                 FStar_Tactics_Embedding.embed_proofstate proof_state in
               FStar_Syntax_Syntax.as_arg uu____1223 in
             [uu____1222] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1221 in
         uu____1220 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____1230 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1235  ->
              let uu____1236 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1236) in
       FStar_Tactics_Basic.bind uu____1230
         (fun uu____1237  ->
            let result =
              let uu____1239 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1239 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____1241 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1246  ->
                   let uu____1247 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1247) in
            FStar_Tactics_Basic.bind uu____1241
              (fun uu____1248  ->
                 let uu____1249 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____1249 with
                 | FStar_Util.Inl (b,ps) ->
                     let uu____1263 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1263
                       (fun uu____1265  -> FStar_Tactics_Basic.ret b)
                 | FStar_Util.Inr (msg,ps) ->
                     let uu____1272 = FStar_Tactics_Basic.set ps in
                     FStar_Tactics_Basic.bind uu____1272
                       (fun uu____1274  -> FStar_Tactics_Basic.fail msg))))
let run_tactic_on_typ tau env typ =
  let uu____1297 = FStar_TypeChecker_Env.clear_expected_typ env in
  match uu____1297 with
  | (env1,uu____1305) ->
      let env2 =
        let uu___106_1309 = env1 in
        {
          FStar_TypeChecker_Env.solver =
            (uu___106_1309.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___106_1309.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___106_1309.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___106_1309.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___106_1309.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___106_1309.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___106_1309.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___106_1309.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___106_1309.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___106_1309.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___106_1309.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___106_1309.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___106_1309.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___106_1309.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___106_1309.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___106_1309.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___106_1309.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___106_1309.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___106_1309.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___106_1309.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___106_1309.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___106_1309.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___106_1309.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___106_1309.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___106_1309.FStar_TypeChecker_Env.synth)
        } in
      let uu____1310 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
      (match uu____1310 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps) in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1329,ps1) ->
                ((let uu____1332 = FStar_ST.read tacdbg in
                  if uu____1332
                  then
                    let uu____1335 = FStar_Syntax_Print.term_to_string w in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1335
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1339 = FStar_Tactics_Basic.is_irrelevant g in
                      if uu____1339
                      then
                        let uu____1340 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Const.exp_unit in
                        (if uu____1340
                         then ()
                         else
                           (let uu____1342 =
                              let uu____1343 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1343 in
                            failwith uu____1342))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___109_1346 = FStar_TypeChecker_Rel.trivial_guard in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___109_1346.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___109_1346.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___109_1346.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    } in
                  let g1 =
                    let uu____1348 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g in
                    FStar_All.pipe_right uu____1348
                      FStar_TypeChecker_Rel.resolve_implicits_lax in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                let uu____1353 =
                  let uu____1354 =
                    let uu____1357 =
                      FStar_Util.format1 "user tactic failed: %s" s in
                    (uu____1357, (typ.FStar_Syntax_Syntax.pos)) in
                  FStar_Errors.Error uu____1354 in
                raise uu____1353))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1364 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1368 -> false
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
        let uu____1387 = FStar_Syntax_Util.head_and_args t in
        match uu____1387 with
        | (hd1,args) ->
            let uu____1416 =
              let uu____1424 =
                let uu____1425 = FStar_Syntax_Util.un_uinst hd1 in
                uu____1425.FStar_Syntax_Syntax.n in
              (uu____1424, args) in
            (match uu____1416 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1438)::(tactic,uu____1440)::(assertion,uu____1442)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1481)::(tactic,uu____1483)::(assertion,uu____1485)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let uu____1519 =
                   let uu____1523 =
                     unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                       tactic in
                   run_tactic_on_typ uu____1523 e assertion in
                 (match uu____1519 with
                  | (gs,uu____1529) -> (FStar_Syntax_Util.t_true, gs))
             | uu____1533 -> (t, []))
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
          let uu____1581 =
            let uu____1585 =
              let uu____1586 = FStar_Syntax_Subst.compress t in
              uu____1586.FStar_Syntax_Syntax.n in
            match uu____1585 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1598 = traverse f pol e t1 in
                (match uu____1598 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1616 = traverse f pol e t1 in
                (match uu____1616 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1629;
                   FStar_Syntax_Syntax.pos = uu____1630;
                   FStar_Syntax_Syntax.vars = uu____1631;_},(p,uu____1633)::
                 (q,uu____1635)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p in
                let uu____1666 =
                  let uu____1670 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1670 p in
                (match uu____1666 with
                 | (p',gs1) ->
                     let uu____1678 =
                       let uu____1682 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1682 q in
                     (match uu____1678 with
                      | (q',gs2) ->
                          let uu____1690 =
                            let uu____1691 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1691.FStar_Syntax_Syntax.n in
                          (uu____1690, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1711 = traverse f pol e hd1 in
                (match uu____1711 with
                 | (hd',gs1) ->
                     let uu____1722 =
                       FStar_List.fold_right
                         (fun uu____1737  ->
                            fun uu____1738  ->
                              match (uu____1737, uu____1738) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1781 = traverse f pol e a in
                                  (match uu____1781 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1722 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1849 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1849 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1858 =
                       let uu____1866 =
                         FStar_List.map
                           (fun uu____1880  ->
                              match uu____1880 with
                              | (bv,aq) ->
                                  let uu____1890 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____1890 with
                                   | (s',gs) ->
                                       (((let uu___110_1906 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___110_1906.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___110_1906.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____1866 in
                     (match uu____1858 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____1940 = traverse f pol e' topen in
                          (match uu____1940 with
                           | (topen',gs2) ->
                               let uu____1951 =
                                 let uu____1952 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____1952.FStar_Syntax_Syntax.n in
                               (uu____1951, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____1581 with
          | (tn',gs) ->
              let t' =
                let uu___111_1968 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___111_1968.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___111_1968.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___111_1968.FStar_Syntax_Syntax.vars)
                } in
              let uu____1973 = f pol e t' in
              (match uu____1973 with
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
      let uu____1994 = FStar_Syntax_Util.un_squash tn in
      match uu____1994 with
      | Some t' -> Some t'
      | None  ->
          let uu____2008 = FStar_Syntax_Util.head_and_args tn in
          (match uu____2008 with
           | (hd1,uu____2020) ->
               let uu____2035 =
                 let uu____2036 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____2036.FStar_Syntax_Syntax.n in
               (match uu____2035 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid
                    -> Some t
                | uu____2041 -> None))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____2055 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____2055);
      (let uu____2059 = FStar_ST.read tacdbg in
       if uu____2059
       then
         let uu____2062 =
           let uu____2063 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____2063
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____2064 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2062
           uu____2064
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____2077 = traverse by_tactic_interp Pos env goal in
       match uu____2077 with
       | (t',gs) ->
           ((let uu____2089 = FStar_ST.read tacdbg in
             if uu____2089
             then
               let uu____2092 =
                 let uu____2093 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____2093
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____2094 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2092 uu____2094
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2113  ->
                    fun g  ->
                      match uu____2113 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2134 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty in
                            match uu____2134 with
                            | None  ->
                                let uu____2136 =
                                  let uu____2137 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2137 in
                                failwith uu____2136
                            | Some phi -> phi in
                          ((let uu____2140 = FStar_ST.read tacdbg in
                            if uu____2140
                            then
                              let uu____2143 = FStar_Util.string_of_int n1 in
                              let uu____2144 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2143 uu____2144
                            else ());
                           (let gt' =
                              let uu____2147 =
                                let uu____2148 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____2148 in
                              FStar_TypeChecker_Util.label uu____2147
                                FStar_Range.dummyRange phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____2154 = s1 in
             match uu____2154 with | (uu____2163,gs1) -> (env, t') :: gs1)))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____2177 =
        let uu____2178 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational None in
        FStar_Syntax_Syntax.fv_to_tm uu____2178 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____2177 [FStar_Syntax_Syntax.U_zero] in
    let uu____2179 =
      let uu____2180 =
        let uu____2181 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____2182 =
          let uu____2184 = FStar_Syntax_Syntax.as_arg a in [uu____2184] in
        uu____2181 :: uu____2182 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____2180 in
    uu____2179 None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____2198 =
          let uu____2202 =
            let uu____2204 = reify_tactic tau in
            unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____2204 in
          run_tactic_on_typ uu____2202 env typ in
        match uu____2198 with
        | (gs,w) ->
            (match gs with
             | [] -> w
             | uu____2209::uu____2210 ->
                 raise
                   (FStar_Errors.Error
                      ("synthesis left open goals",
                        (typ.FStar_Syntax_Syntax.pos))))