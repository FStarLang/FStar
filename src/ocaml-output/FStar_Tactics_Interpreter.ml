open Prims
let tacdbg : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let t_unit :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_unit 
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____47)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____61  ->
            let uu____62 = FStar_Ident.string_of_lid nm  in
            let uu____63 = FStar_Syntax_Print.args_to_string args  in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____62 uu____63);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state  in
        let res = FStar_Tactics_Basic.run t ps1  in
        let uu____67 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a  in
        Some uu____67))
  | uu____68 -> failwith "Unexpected application of tactic primitive" 
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____128)::(embedded_state,uu____130)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____152  ->
            let uu____153 = FStar_Ident.string_of_lid nm  in
            let uu____154 = FStar_Syntax_Print.term_to_string embedded_state
               in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____153
              uu____154);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state  in
        let res =
          let uu____158 = let uu____160 = unembed_b b  in t uu____160  in
          FStar_Tactics_Basic.run uu____158 ps1  in
        let uu____161 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a  in
        Some uu____161))
  | uu____162 ->
      let uu____163 =
        let uu____164 = FStar_Ident.string_of_lid nm  in
        let uu____165 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____164 uu____165
         in
      failwith uu____163
  
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____242)::(b,uu____244)::(embedded_state,uu____246)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____276  ->
            let uu____277 = FStar_Ident.string_of_lid nm  in
            let uu____278 = FStar_Syntax_Print.term_to_string embedded_state
               in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____277
              uu____278);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state  in
        let res =
          let uu____282 =
            let uu____284 = unembed_a a  in
            let uu____285 = unembed_b b  in t uu____284 uu____285  in
          FStar_Tactics_Basic.run uu____282 ps1  in
        let uu____286 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c  in
        Some uu____286))
  | uu____287 ->
      let uu____288 =
        let uu____289 = FStar_Ident.string_of_lid nm  in
        let uu____290 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____289 uu____290
         in
      failwith uu____288
  
let mk_tactic_interpretation_3 ps t unembed_a unembed_b unembed_c embed_d t_d
  nm args =
  match args with
  | (a,uu____384)::(b,uu____386)::(c,uu____388)::(embedded_state,uu____390)::[]
      ->
      (FStar_Tactics_Basic.log ps
         (fun uu____428  ->
            let uu____429 = FStar_Ident.string_of_lid nm  in
            let uu____430 = FStar_Syntax_Print.term_to_string embedded_state
               in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____429
              uu____430);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state  in
        let res =
          let uu____434 =
            let uu____436 = unembed_a a  in
            let uu____437 = unembed_b b  in
            let uu____438 = unembed_c c  in t uu____436 uu____437 uu____438
             in
          FStar_Tactics_Basic.run uu____434 ps1  in
        let uu____439 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_d t_d  in
        Some uu____439))
  | uu____440 ->
      let uu____441 =
        let uu____442 = FStar_Ident.string_of_lid nm  in
        let uu____443 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____442 uu____443
         in
      failwith uu____441
  
let mk_tactic_interpretation_5 ps t unembed_a unembed_b unembed_c unembed_d
  unembed_e embed_f t_f nm args =
  match args with
  | (a,uu____571)::(b,uu____573)::(c,uu____575)::(d,uu____577)::(e,uu____579)::
      (embedded_state,uu____581)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____635  ->
            let uu____636 = FStar_Ident.string_of_lid nm  in
            let uu____637 = FStar_Syntax_Print.term_to_string embedded_state
               in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____636
              uu____637);
       (let ps1 =
          FStar_Tactics_Embedding.unembed_proofstate ps embedded_state  in
        let res =
          let uu____641 =
            let uu____643 = unembed_a a  in
            let uu____644 = unembed_b b  in
            let uu____645 = unembed_c c  in
            let uu____646 = unembed_d d  in
            let uu____647 = unembed_e e  in
            t uu____643 uu____644 uu____645 uu____646 uu____647  in
          FStar_Tactics_Basic.run uu____641 ps1  in
        let uu____648 =
          FStar_Tactics_Embedding.embed_result ps1 res embed_f t_f  in
        Some uu____648))
  | uu____649 ->
      let uu____650 =
        let uu____651 = FStar_Ident.string_of_lid nm  in
        let uu____652 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____651 uu____652
         in
      failwith uu____650
  
let step_from_native_step :
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____661 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name
          in
       FStar_Util.print1 "Registered primitive step %s\n" uu____661);
      {
        FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Normalize.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Normalize.interpretation =
          ((fun _rng  -> fun args  -> s.FStar_Tactics_Native.tactic ps args))
      }
  
let rec primitive_steps :
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  fun ps  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm]
         in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      }  in
    let native_tactics = FStar_Tactics_Native.list_all ()  in
    let native_tactics_steps =
      FStar_List.map (step_from_native_step ps) native_tactics  in
    let mk_refl nm arity interpretation =
      let nm1 = FStar_Reflection_Data.fstar_refl_lid nm  in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      }  in
    let mktac0 name f e_a ta =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 ps f e_a ta)
       in
    let mktac1 name f u_a e_b tb =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 ps f u_a e_b tb)
       in
    let mktac2 name f u_a u_b e_c tc =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 ps f u_a u_b e_c tc)
       in
    let mktac3 name f u_a u_b u_c e_d tc =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 ps f u_a u_b u_c e_d tc)
       in
    let mktac5 name f u_a u_b u_c u_d u_e e_f tc =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 ps f u_a u_b u_c u_d u_e e_f tc)
       in
    let binders_of_env_int nm args =
      match args with
      | (e,uu____1097)::[] ->
          let uu____1102 =
            let uu____1103 =
              let uu____1105 = FStar_Tactics_Embedding.unembed_env ps e  in
              FStar_TypeChecker_Env.all_binders uu____1105  in
            FStar_Reflection_Basic.embed_binders uu____1103  in
          Some uu____1102
      | uu____1106 ->
          let uu____1110 =
            let uu____1111 = FStar_Ident.string_of_lid nm  in
            let uu____1112 = FStar_Syntax_Print.args_to_string args  in
            FStar_Util.format2 "Unexpected application %s %s" uu____1111
              uu____1112
             in
          failwith uu____1110
       in
    let uu____1114 =
      let uu____1116 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit
         in
      let uu____1117 =
        let uu____1119 =
          mktac2 "__trytac" (fun uu____1122  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit
           in
        let uu____1126 =
          let uu____1128 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder
             in
          let uu____1131 =
            let uu____1133 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit
               in
            let uu____1135 =
              let uu____1137 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit
                 in
              let uu____1138 =
                let uu____1140 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit
                   in
                let uu____1141 =
                  let uu____1143 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit
                     in
                  let uu____1144 =
                    let uu____1146 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit
                       in
                    let uu____1147 =
                      let uu____1149 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit
                         in
                      let uu____1150 =
                        let uu____1152 =
                          mktac1 "__exact_lemma"
                            FStar_Tactics_Basic.exact_lemma
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit
                           in
                        let uu____1153 =
                          let uu____1155 =
                            mktac1 "__apply" FStar_Tactics_Basic.apply
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit
                             in
                          let uu____1156 =
                            let uu____1158 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit
                               in
                            let uu____1159 =
                              let uu____1161 =
                                mktac5 "__divide"
                                  (fun uu____1166  ->
                                     fun uu____1167  ->
                                       FStar_Tactics_Basic.divide)
                                  (fun t  -> t) (fun t  -> t)
                                  FStar_Reflection_Basic.unembed_int
                                  (unembed_tactic_0 (fun t  -> t))
                                  (unembed_tactic_0 (fun t  -> t))
                                  (FStar_Reflection_Basic.embed_pair
                                     (fun t  -> t) t_unit (fun t  -> t)
                                     t_unit) t_unit
                                 in
                              let uu____1174 =
                                let uu____1176 =
                                  mktac1 "__set_options"
                                    FStar_Tactics_Basic.set_options
                                    FStar_Reflection_Basic.unembed_string
                                    FStar_Reflection_Basic.embed_unit t_unit
                                   in
                                let uu____1177 =
                                  let uu____1179 =
                                    mktac2 "__seq" FStar_Tactics_Basic.seq
                                      (unembed_tactic_0
                                         FStar_Reflection_Basic.unembed_unit)
                                      (unembed_tactic_0
                                         FStar_Reflection_Basic.unembed_unit)
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit
                                     in
                                  let uu____1182 =
                                    let uu____1184 =
                                      mktac1 "__prune"
                                        FStar_Tactics_Basic.prune
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit
                                       in
                                    let uu____1185 =
                                      let uu____1187 =
                                        mktac1 "__addns"
                                          FStar_Tactics_Basic.addns
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit
                                         in
                                      let uu____1188 =
                                        let uu____1190 =
                                          mktac1 "__print"
                                            (fun x  ->
                                               FStar_Tactics_Basic.tacprint x;
                                               FStar_Tactics_Basic.ret ())
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit
                                           in
                                        let uu____1193 =
                                          let uu____1195 =
                                            mktac1 "__dump"
                                              FStar_Tactics_Basic.print_proof_state
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit
                                             in
                                          let uu____1196 =
                                            let uu____1198 =
                                              mktac1 "__dump1"
                                                FStar_Tactics_Basic.print_proof_state1
                                                FStar_Reflection_Basic.unembed_string
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit
                                               in
                                            let uu____1199 =
                                              let uu____1201 =
                                                mktac1 "__pointwise"
                                                  FStar_Tactics_Basic.pointwise
                                                  (unembed_tactic_0
                                                     FStar_Reflection_Basic.unembed_unit)
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit
                                                 in
                                              let uu____1203 =
                                                let uu____1205 =
                                                  mktac0 "__trefl"
                                                    FStar_Tactics_Basic.trefl
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit
                                                   in
                                                let uu____1206 =
                                                  let uu____1208 =
                                                    mktac0 "__later"
                                                      FStar_Tactics_Basic.later
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit
                                                     in
                                                  let uu____1209 =
                                                    let uu____1211 =
                                                      mktac0 "__flip"
                                                        FStar_Tactics_Basic.flip
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit
                                                       in
                                                    let uu____1212 =
                                                      let uu____1214 =
                                                        mktac0 "__qed"
                                                          FStar_Tactics_Basic.qed
                                                          FStar_Reflection_Basic.embed_unit
                                                          t_unit
                                                         in
                                                      let uu____1215 =
                                                        let uu____1217 =
                                                          let uu____1218 =
                                                            FStar_Tactics_Embedding.pair_typ
                                                              FStar_Reflection_Data.fstar_refl_term
                                                              FStar_Reflection_Data.fstar_refl_term
                                                             in
                                                          mktac1 "__cases"
                                                            FStar_Tactics_Basic.cases
                                                            FStar_Reflection_Basic.unembed_term
                                                            (FStar_Reflection_Basic.embed_pair
                                                               FStar_Reflection_Basic.embed_term
                                                               FStar_Reflection_Data.fstar_refl_term
                                                               FStar_Reflection_Basic.embed_term
                                                               FStar_Reflection_Data.fstar_refl_term)
                                                            uu____1218
                                                           in
                                                        let uu____1221 =
                                                          let uu____1223 =
                                                            mk_refl
                                                              ["Syntax";
                                                              "__binders_of_env"]
                                                              (Prims.parse_int "1")
                                                              binders_of_env_int
                                                             in
                                                          let uu____1224 =
                                                            let uu____1226 =
                                                              mktac0
                                                                "__cur_env"
                                                                FStar_Tactics_Basic.cur_env
                                                                (FStar_Tactics_Embedding.embed_env
                                                                   ps)
                                                                FStar_Reflection_Data.fstar_refl_env
                                                               in
                                                            let uu____1227 =
                                                              let uu____1229
                                                                =
                                                                mktac0
                                                                  "__cur_goal"
                                                                  FStar_Tactics_Basic.cur_goal'
                                                                  FStar_Reflection_Basic.embed_term
                                                                  FStar_Reflection_Data.fstar_refl_term
                                                                 in
                                                              let uu____1230
                                                                =
                                                                let uu____1232
                                                                  =
                                                                  mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Reflection_Data.fstar_refl_term
                                                                   in
                                                                [uu____1232]
                                                                 in
                                                              uu____1229 ::
                                                                uu____1230
                                                               in
                                                            uu____1226 ::
                                                              uu____1227
                                                             in
                                                          uu____1223 ::
                                                            uu____1224
                                                           in
                                                        uu____1217 ::
                                                          uu____1221
                                                         in
                                                      uu____1214 ::
                                                        uu____1215
                                                       in
                                                    uu____1211 :: uu____1212
                                                     in
                                                  uu____1208 :: uu____1209
                                                   in
                                                uu____1205 :: uu____1206  in
                                              uu____1201 :: uu____1203  in
                                            uu____1198 :: uu____1199  in
                                          uu____1195 :: uu____1196  in
                                        uu____1190 :: uu____1193  in
                                      uu____1187 :: uu____1188  in
                                    uu____1184 :: uu____1185  in
                                  uu____1179 :: uu____1182  in
                                uu____1176 :: uu____1177  in
                              uu____1161 :: uu____1174  in
                            uu____1158 :: uu____1159  in
                          uu____1155 :: uu____1156  in
                        uu____1152 :: uu____1153  in
                      uu____1149 :: uu____1150  in
                    uu____1146 :: uu____1147  in
                  uu____1143 :: uu____1144  in
                uu____1140 :: uu____1141  in
              uu____1137 :: uu____1138  in
            uu____1133 :: uu____1135  in
          uu____1128 :: uu____1131  in
        uu____1119 :: uu____1126  in
      uu____1116 :: uu____1117  in
    FStar_List.append uu____1114
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)

and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____1241 =
           let uu____1242 =
             let uu____1243 =
               let uu____1244 =
                 FStar_Tactics_Embedding.embed_proofstate proof_state  in
               FStar_Syntax_Syntax.as_arg uu____1244  in
             [uu____1243]  in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1242  in
         uu____1241 None FStar_Range.dummyRange  in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops]  in
       let uu____1251 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____1256  ->
              let uu____1257 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1257)
          in
       FStar_Tactics_Basic.bind uu____1251
         (fun uu____1258  ->
            let result =
              let uu____1260 = primitive_steps proof_state  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1260 steps proof_state.FStar_Tactics_Basic.main_context
                tm
               in
            let uu____1262 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____1267  ->
                   let uu____1268 = FStar_Syntax_Print.term_to_string result
                      in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____1268)
               in
            FStar_Tactics_Basic.bind uu____1262
              (fun uu____1269  ->
                 let uu____1270 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b
                    in
                 match uu____1270 with
                 | FStar_Util.Inl (b,ps) ->
                     let uu____1284 = FStar_Tactics_Basic.set ps  in
                     FStar_Tactics_Basic.bind uu____1284
                       (fun uu____1286  -> FStar_Tactics_Basic.ret b)
                 | FStar_Util.Inr (msg,ps) ->
                     let uu____1293 = FStar_Tactics_Basic.set ps  in
                     FStar_Tactics_Basic.bind uu____1293
                       (fun uu____1295  -> FStar_Tactics_Basic.fail msg))))

let run_tactic_on_typ tau env typ =
  let uu____1318 = FStar_TypeChecker_Env.clear_expected_typ env  in
  match uu____1318 with
  | (env1,uu____1326) ->
      let env2 =
        let uu___108_1330 = env1  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___108_1330.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___108_1330.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___108_1330.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___108_1330.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___108_1330.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___108_1330.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___108_1330.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___108_1330.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___108_1330.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp = false;
          FStar_TypeChecker_Env.effects =
            (uu___108_1330.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___108_1330.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___108_1330.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___108_1330.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___108_1330.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___108_1330.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___108_1330.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___108_1330.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___108_1330.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___108_1330.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.type_of =
            (uu___108_1330.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___108_1330.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___108_1330.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qname_and_index =
            (uu___108_1330.FStar_TypeChecker_Env.qname_and_index);
          FStar_TypeChecker_Env.proof_ns =
            (uu___108_1330.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth =
            (uu___108_1330.FStar_TypeChecker_Env.synth);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___108_1330.FStar_TypeChecker_Env.is_native_tactic)
        }  in
      let uu____1331 = FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ  in
      (match uu____1331 with
       | (ps,w) ->
           let r =
             try FStar_Tactics_Basic.run tau ps
             with
             | FStar_Tactics_Basic.TacFailure s ->
                 FStar_Tactics_Basic.Failed
                   ((Prims.strcat "EXCEPTION: " s), ps)
              in
           (match r with
            | FStar_Tactics_Basic.Success (uu____1350,ps1) ->
                ((let uu____1353 = FStar_ST.read tacdbg  in
                  if uu____1353
                  then
                    let uu____1356 = FStar_Syntax_Print.term_to_string w  in
                    FStar_Util.print1 "Tactic generated proofterm %s\n"
                      uu____1356
                  else ());
                 FStar_List.iter
                   (fun g  ->
                      let uu____1360 = FStar_Tactics_Basic.is_irrelevant g
                         in
                      if uu____1360
                      then
                        let uu____1361 =
                          FStar_TypeChecker_Rel.teq_nosmt
                            g.FStar_Tactics_Basic.context
                            g.FStar_Tactics_Basic.witness
                            FStar_Syntax_Const.exp_unit
                           in
                        (if uu____1361
                         then ()
                         else
                           (let uu____1363 =
                              let uu____1364 =
                                FStar_Syntax_Print.term_to_string
                                  g.FStar_Tactics_Basic.witness
                                 in
                              FStar_Util.format1
                                "Irrelevant tactic witness does not unify with (): %s"
                                uu____1364
                               in
                            failwith uu____1363))
                      else ())
                   (FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals);
                 (let g =
                    let uu___111_1367 = FStar_TypeChecker_Rel.trivial_guard
                       in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___111_1367.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___111_1367.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___111_1367.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        (ps1.FStar_Tactics_Basic.all_implicits)
                    }  in
                  let g1 =
                    let uu____1369 =
                      FStar_TypeChecker_Rel.solve_deferred_constraints env2 g
                       in
                    FStar_All.pipe_right uu____1369
                      FStar_TypeChecker_Rel.resolve_implicits_lax
                     in
                  FStar_TypeChecker_Rel.force_trivial_guard env2 g1;
                  ((FStar_List.append ps1.FStar_Tactics_Basic.goals
                      ps1.FStar_Tactics_Basic.smt_goals), w)))
            | FStar_Tactics_Basic.Failed (s,ps1) ->
                let uu____1374 =
                  let uu____1375 =
                    let uu____1378 =
                      FStar_Util.format1 "user tactic failed: %s" s  in
                    (uu____1378, (typ.FStar_Syntax_Syntax.pos))  in
                  FStar_Errors.Error uu____1375  in
                raise uu____1374))
  
type pol =
  | Pos 
  | Neg 
let uu___is_Pos : pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____1385 -> false 
let uu___is_Neg : pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____1389 -> false 
let flip : pol -> pol = fun p  -> match p with | Pos  -> Neg | Neg  -> Pos 
let by_tactic_interp :
  pol ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Tactics_Basic.goal Prims.list)
  =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1408 = FStar_Syntax_Util.head_and_args t  in
        match uu____1408 with
        | (hd1,args) ->
            let uu____1437 =
              let uu____1445 =
                let uu____1446 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1446.FStar_Syntax_Syntax.n  in
              (uu____1445, args)  in
            (match uu____1437 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1459)::(tactic,uu____1461)::(assertion,uu____1463)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____1502)::(tactic,uu____1504)::(assertion,uu____1506)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let uu____1540 =
                   let uu____1544 =
                     unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                       tactic
                      in
                   run_tactic_on_typ uu____1544 e assertion  in
                 (match uu____1540 with
                  | (gs,uu____1550) -> (FStar_Syntax_Util.t_true, gs))
             | uu____1554 -> (t, []))
  
let rec traverse :
  (pol ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term * FStar_Tactics_Basic.goal Prims.list))
    ->
    pol ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Tactics_Basic.goal Prims.list)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let uu____1602 =
            let uu____1606 =
              let uu____1607 = FStar_Syntax_Subst.compress t  in
              uu____1607.FStar_Syntax_Syntax.n  in
            match uu____1606 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1619 = traverse f pol e t1  in
                (match uu____1619 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1637 = traverse f pol e t1  in
                (match uu____1637 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1650;
                   FStar_Syntax_Syntax.pos = uu____1651;
                   FStar_Syntax_Syntax.vars = uu____1652;_},(p,uu____1654)::
                 (q,uu____1656)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p  in
                let uu____1687 =
                  let uu____1691 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f (flip pol) uu____1691 p  in
                (match uu____1687 with
                 | (p',gs1) ->
                     let uu____1699 =
                       let uu____1703 = FStar_TypeChecker_Env.push_bv e x  in
                       traverse f pol uu____1703 q  in
                     (match uu____1699 with
                      | (q',gs2) ->
                          let uu____1711 =
                            let uu____1712 = FStar_Syntax_Util.mk_imp p' q'
                               in
                            uu____1712.FStar_Syntax_Syntax.n  in
                          (uu____1711, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1732 = traverse f pol e hd1  in
                (match uu____1732 with
                 | (hd',gs1) ->
                     let uu____1743 =
                       FStar_List.fold_right
                         (fun uu____1758  ->
                            fun uu____1759  ->
                              match (uu____1758, uu____1759) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1802 = traverse f pol e a  in
                                  (match uu____1802 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], [])
                        in
                     (match uu____1743 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1860 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____1860 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let uu____1869 =
                       let uu____1877 =
                         FStar_List.map
                           (fun uu____1891  ->
                              match uu____1891 with
                              | (bv,aq) ->
                                  let uu____1901 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort
                                     in
                                  (match uu____1901 with
                                   | (s',gs) ->
                                       (((let uu___112_1917 = bv  in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___112_1917.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___112_1917.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1
                          in
                       FStar_All.pipe_left FStar_List.unzip uu____1877  in
                     (match uu____1869 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1  in
                          let uu____1951 = traverse f pol e' topen  in
                          (match uu____1951 with
                           | (topen',gs2) ->
                               let uu____1962 =
                                 let uu____1963 =
                                   FStar_Syntax_Util.abs bs2 topen' k  in
                                 uu____1963.FStar_Syntax_Syntax.n  in
                               (uu____1962, (FStar_List.append gs11 gs2)))))
            | x -> (x, [])  in
          match uu____1602 with
          | (tn',gs) ->
              let t' =
                let uu___113_1979 = t  in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___113_1979.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___113_1979.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___113_1979.FStar_Syntax_Syntax.vars)
                }  in
              let uu____1984 = f pol e t'  in
              (match uu____1984 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
  
let getprop :
  FStar_Tactics_Basic.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t
         in
      let uu____2005 = FStar_Syntax_Util.un_squash tn  in
      match uu____2005 with
      | Some t' -> Some t'
      | None  ->
          let uu____2019 = FStar_Syntax_Util.head_and_args tn  in
          (match uu____2019 with
           | (hd1,uu____2031) ->
               let uu____2046 =
                 let uu____2047 = FStar_Syntax_Util.un_uinst hd1  in
                 uu____2047.FStar_Syntax_Syntax.n  in
               (match uu____2046 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid
                    -> Some t
                | uu____2052 -> None))
  
let preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
        FStar_Options.optionstate) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____2068 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.write tacdbg uu____2068);
      (let uu____2072 = FStar_ST.read tacdbg  in
       if uu____2072
       then
         let uu____2075 =
           let uu____2076 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____2076
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____2077 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2075
           uu____2077
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____2093 = traverse by_tactic_interp Pos env goal  in
       match uu____2093 with
       | (t',gs) ->
           ((let uu____2106 = FStar_ST.read tacdbg  in
             if uu____2106
             then
               let uu____2109 =
                 let uu____2110 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____2110
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____2111 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2109 uu____2111
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____2133  ->
                    fun g  ->
                      match uu____2133 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____2158 =
                              getprop g.FStar_Tactics_Basic.context
                                g.FStar_Tactics_Basic.goal_ty
                               in
                            match uu____2158 with
                            | None  ->
                                let uu____2160 =
                                  let uu____2161 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Basic.goal_ty
                                     in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____2161
                                   in
                                failwith uu____2160
                            | Some phi -> phi  in
                          ((let uu____2164 = FStar_ST.read tacdbg  in
                            if uu____2164
                            then
                              let uu____2167 = FStar_Util.string_of_int n1
                                 in
                              let uu____2168 =
                                FStar_Tactics_Basic.goal_to_string g  in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____2167 uu____2168
                            else ());
                           (let gt' =
                              let uu____2171 =
                                let uu____2172 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____2172
                                 in
                              FStar_TypeChecker_Util.label uu____2171
                                FStar_Range.dummyRange phi
                               in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt',
                                 (g.FStar_Tactics_Basic.opts)) :: gs1))))) s
                 gs
                in
             let uu____2180 = s1  in
             match uu____2180 with
             | (uu____2191,gs1) ->
                 let uu____2201 =
                   let uu____2205 = FStar_Options.peek ()  in
                   (env, t', uu____2205)  in
                 uu____2201 :: gs1)))
  
let reify_tactic :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____2213 =
        let uu____2214 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____2214  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____2213 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____2215 =
      let uu____2216 =
        let uu____2217 = FStar_Syntax_Syntax.iarg t_unit  in
        let uu____2218 =
          let uu____2220 = FStar_Syntax_Syntax.as_arg a  in [uu____2220]  in
        uu____2217 :: uu____2218  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____2216  in
    uu____2215 None a.FStar_Syntax_Syntax.pos
  
let synth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let uu____2234 =
          let uu____2238 =
            let uu____2240 = reify_tactic tau  in
            unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____2240
             in
          run_tactic_on_typ uu____2238 env typ  in
        match uu____2234 with
        | (gs,w) ->
            (match gs with
             | [] -> w
             | uu____2245::uu____2246 ->
                 raise
                   (FStar_Errors.Error
                      ("synthesis left open goals",
                        (typ.FStar_Syntax_Syntax.pos))))
  