open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let unembed :
  'uuuuuu14 .
    'uuuuuu14 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuuu14 FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a ->
      fun norm_cb ->
        let uu____38 = FStar_Syntax_Embeddings.unembed ea a in
        uu____38 true norm_cb
let embed :
  'uuuuuu57 .
    'uuuuuu57 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuuu57 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu____84 = FStar_Syntax_Embeddings.embed ea x in
          uu____84 r FStar_Pervasives_Native.None norm_cb
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____100 ->
    let step_from_native_step s =
      {
        FStar_TypeChecker_Cfg.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Cfg.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Cfg.univ_arity = Prims.int_zero;
        FStar_TypeChecker_Cfg.auto_reflect =
          (FStar_Pervasives_Native.Some
             (s.FStar_Tactics_Native.arity - Prims.int_one));
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution = false;
        FStar_TypeChecker_Cfg.interpretation =
          (s.FStar_Tactics_Native.tactic);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (fun _cb ->
             FStar_TypeChecker_NBETerm.dummy_interp
               s.FStar_Tactics_Native.name)
      } in
    let uu____113 = FStar_Tactics_Native.list_all () in
    FStar_List.map step_from_native_step uu____113
let mk_total_step_1' :
  'uuuuuu141 'uuuuuu142 'uuuuuu143 'uuuuuu144 .
    Prims.int ->
      Prims.string ->
        ('uuuuuu141 -> 'uuuuuu142) ->
          'uuuuuu141 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu142 FStar_Syntax_Embeddings.embedding ->
              ('uuuuuu143 -> 'uuuuuu144) ->
                'uuuuuu143 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuuu144 FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun er ->
            fun nf ->
              fun ena ->
                fun enr ->
                  let uu___19_215 =
                    FStar_Tactics_InterpFuns.mk_total_step_1 uarity nm f ea
                      er nf ena enr in
                  let uu____216 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu____216;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___19_215.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___19_215.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___19_215.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___19_215.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___19_215.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___19_215.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___19_215.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_1'_psc :
  'uuuuuu243 'uuuuuu244 'uuuuuu245 'uuuuuu246 .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'uuuuuu243 -> 'uuuuuu244) ->
          'uuuuuu243 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu244 FStar_Syntax_Embeddings.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'uuuuuu245 -> 'uuuuuu246) ->
                'uuuuuu245 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuuu246 FStar_TypeChecker_NBETerm.embedding ->
                    FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun er ->
            fun nf ->
              fun ena ->
                fun enr ->
                  let uu___29_327 =
                    FStar_Tactics_InterpFuns.mk_total_step_1_psc uarity nm f
                      ea er nf ena enr in
                  let uu____328 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu____328;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___29_327.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___29_327.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___29_327.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___29_327.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___29_327.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___29_327.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___29_327.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_2' :
  'uuuuuu363 'uuuuuu364 'uuuuuu365 'uuuuuu366 'uuuuuu367 'uuuuuu368 .
    Prims.int ->
      Prims.string ->
        ('uuuuuu363 -> 'uuuuuu364 -> 'uuuuuu365) ->
          'uuuuuu363 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu364 FStar_Syntax_Embeddings.embedding ->
              'uuuuuu365 FStar_Syntax_Embeddings.embedding ->
                ('uuuuuu366 -> 'uuuuuu367 -> 'uuuuuu368) ->
                  'uuuuuu366 FStar_TypeChecker_NBETerm.embedding ->
                    'uuuuuu367 FStar_TypeChecker_NBETerm.embedding ->
                      'uuuuuu368 FStar_TypeChecker_NBETerm.embedding ->
                        FStar_TypeChecker_Cfg.primitive_step
  =
  fun uarity ->
    fun nm ->
      fun f ->
        fun ea ->
          fun eb ->
            fun er ->
              fun nf ->
                fun ena ->
                  fun enb ->
                    fun enr ->
                      let uu___41_467 =
                        FStar_Tactics_InterpFuns.mk_total_step_2 uarity nm f
                          ea eb er nf ena enb enr in
                      let uu____468 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm) in
                      {
                        FStar_TypeChecker_Cfg.name = uu____468;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___41_467.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___41_467.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___41_467.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___41_467.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___41_467.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___41_467.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___41_467.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
let (__primitive_steps_ref :
  FStar_TypeChecker_Cfg.primitive_step Prims.list
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____490 ->
    let uu____493 =
      let uu____496 = FStar_ST.op_Bang __primitive_steps_ref in
      FStar_Util.must uu____496 in
    let uu____530 = native_tactics_steps () in
    FStar_List.append uu____493 uu____530
let unembed_tactic_0 :
  'b .
    'b FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'b FStar_Tactics_Monad.tac
  =
  fun eb ->
    fun embedded_tac_b ->
      fun ncb ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos in
             let embedded_tac_b1 = FStar_Syntax_Util.mk_reify embedded_tac_b in
             let tm =
               let uu____583 =
                 let uu____584 =
                   let uu____593 =
                     embed FStar_Tactics_Embedding.e_proofstate rng
                       proof_state ncb in
                   FStar_Syntax_Syntax.as_arg uu____593 in
                 [uu____584] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____583 rng in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe] in
             let norm_f =
               let uu____634 = FStar_Options.tactics_nbe () in
               if uu____634
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps in
             let result =
               let uu____656 = primitive_steps () in
               norm_f uu____656 steps
                 proof_state.FStar_Tactics_Types.main_context tm in
             let res =
               let uu____664 = FStar_Tactics_Embedding.e_result eb in
               unembed uu____664 result ncb in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu____677 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____677
                   (fun uu____681 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu____686 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____686
                   (fun uu____690 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu____693 =
                   let uu____699 =
                     let uu____701 = FStar_Syntax_Print.term_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____701 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____699) in
                 FStar_Errors.raise_error uu____693
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)
let unembed_tactic_nbe_0 :
  'b .
    'b FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'b FStar_Tactics_Monad.tac
  =
  fun eb ->
    fun cb ->
      fun embedded_tac_b ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state ->
             let result =
               let uu____746 =
                 let uu____747 =
                   let uu____752 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state in
                   FStar_TypeChecker_NBETerm.as_arg uu____752 in
                 [uu____747] in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____746 in
             let res =
               let uu____766 = FStar_Tactics_Embedding.e_result_nbe eb in
               FStar_TypeChecker_NBETerm.unembed uu____766 cb result in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu____779 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____779
                   (fun uu____783 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu____788 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____788
                   (fun uu____792 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu____795 =
                   let uu____801 =
                     let uu____803 =
                       FStar_TypeChecker_NBETerm.t_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____803 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____801) in
                 FStar_Errors.raise_error uu____795
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)
let unembed_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb -> 'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          fun x ->
            let rng = FStar_Range.dummyRange in
            let x_tm = embed ea rng x ncb in
            let app =
              let uu____863 =
                let uu____864 = FStar_Syntax_Syntax.as_arg x_tm in
                [uu____864] in
              FStar_Syntax_Syntax.mk_Tm_app f uu____863 rng in
            unembed_tactic_0 er app ncb
let unembed_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea ->
    fun er ->
      fun cb ->
        fun f ->
          fun x ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x in
            let app =
              let uu____940 =
                let uu____941 = FStar_TypeChecker_NBETerm.as_arg x_tm in
                [uu____941] in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____940 in
            unembed_tactic_nbe_0 er cb app
let e_tactic_thunk :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er ->
    let uu____973 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____980 ->
         fun uu____981 ->
           fun uu____982 ->
             fun uu____983 ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t ->
         fun w ->
           fun cb ->
             let uu____997 =
               let uu____1000 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb in
               uu____1000 () in
             FStar_Pervasives_Native.Some uu____997) uu____973
let e_tactic_nbe_thunk :
  'r .
    'r FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er ->
    let uu____1028 =
      FStar_TypeChecker_NBETerm.mk_t
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
    let uu____1029 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb ->
         fun uu____1035 ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb ->
         fun t ->
           let uu____1044 =
             let uu____1047 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t in
             uu____1047 () in
           FStar_Pervasives_Native.Some uu____1044) uu____1028 uu____1029
let e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    fun er ->
      let uu____1092 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____1102 ->
           fun uu____1103 ->
             fun uu____1104 ->
               fun uu____1105 -> failwith "Impossible: embedding tactic (1)?")
        (fun t ->
           fun w ->
             fun cb ->
               let uu____1121 = unembed_tactic_1 ea er t cb in
               FStar_Pervasives_Native.Some uu____1121) uu____1092
let e_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    fun er ->
      let uu____1169 =
        FStar_TypeChecker_NBETerm.mk_t
          (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
      let uu____1170 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb ->
           fun uu____1179 -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb ->
           fun t ->
             let uu____1190 = unembed_tactic_nbe_1 ea er cb t in
             FStar_Pervasives_Native.Some uu____1190) uu____1169 uu____1170
let (uu___143 : unit) =
  let uu____1203 =
    let uu____1208 =
      let uu____1211 =
        mk_total_step_1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit in
      let uu____1214 =
        let uu____1217 =
          mk_total_step_2' Prims.int_zero "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe in
        let uu____1220 =
          let uu____1223 =
            mk_total_step_1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe in
          let uu____1226 =
            let uu____1229 =
              mk_total_step_1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe in
            let uu____1232 =
              let uu____1235 =
                let uu____1236 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal in
                let uu____1241 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe in
                mk_total_step_1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____1236
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____1241 in
              let uu____1252 =
                let uu____1255 =
                  let uu____1256 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal in
                  let uu____1261 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe in
                  mk_total_step_1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____1256
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____1261 in
                let uu____1272 =
                  let uu____1275 =
                    mk_total_step_1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env in
                  let uu____1278 =
                    let uu____1281 =
                      mk_total_step_1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term in
                    let uu____1284 =
                      let uu____1287 =
                        mk_total_step_1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term in
                      let uu____1290 =
                        let uu____1293 =
                          mk_total_step_1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool in
                        let uu____1298 =
                          let uu____1301 =
                            mk_total_step_1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string in
                          let uu____1306 =
                            let uu____1309 =
                              mk_total_step_2' Prims.int_zero "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe in
                            let uu____1314 =
                              let uu____1317 =
                                let uu____1318 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Tactics_Embedding.e_goal in
                                let uu____1323 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_Tactics_Embedding.e_goal_nbe in
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "set_goals"
                                  FStar_Tactics_Monad.set_goals uu____1318
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Monad.set_goals uu____1323
                                  FStar_TypeChecker_NBETerm.e_unit in
                              let uu____1334 =
                                let uu____1337 =
                                  let uu____1338 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal in
                                  let uu____1343 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe in
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_smt_goals"
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1338 FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1343
                                    FStar_TypeChecker_NBETerm.e_unit in
                                let uu____1354 =
                                  let uu____1357 =
                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "trivial"
                                      FStar_Tactics_Basic.trivial
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.trivial
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit in
                                  let uu____1360 =
                                    let uu____1363 =
                                      let uu____1364 =
                                        e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu____1369 =
                                        FStar_Syntax_Embeddings.e_either
                                          FStar_Tactics_Embedding.e_exn
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu____1376 =
                                        e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any in
                                      let uu____1381 =
                                        FStar_TypeChecker_NBETerm.e_either
                                          FStar_Tactics_Embedding.e_exn_nbe
                                          FStar_TypeChecker_NBETerm.e_any in
                                      FStar_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "catch"
                                        (fun uu____1403 ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_Syntax_Embeddings.e_any
                                        uu____1364 uu____1369
                                        (fun uu____1405 ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu____1376 uu____1381 in
                                    let uu____1406 =
                                      let uu____1409 =
                                        let uu____1410 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu____1415 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu____1422 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any in
                                        let uu____1427 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any in
                                        FStar_Tactics_InterpFuns.mk_tac_step_2
                                          Prims.int_one "recover"
                                          (fun uu____1449 ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____1410 uu____1415
                                          (fun uu____1451 ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____1422 uu____1427 in
                                      let uu____1452 =
                                        let uu____1455 =
                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intro"
                                            FStar_Tactics_Basic.intro
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Tactics_Basic.intro
                                            FStar_TypeChecker_NBETerm.e_unit
                                            FStar_Reflection_NBEEmbeddings.e_binder in
                                        let uu____1458 =
                                          let uu____1461 =
                                            let uu____1462 =
                                              FStar_Syntax_Embeddings.e_tuple2
                                                FStar_Reflection_Embeddings.e_binder
                                                FStar_Reflection_Embeddings.e_binder in
                                            let uu____1469 =
                                              FStar_TypeChecker_NBETerm.e_tuple2
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                FStar_Reflection_NBEEmbeddings.e_binder in
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "intro_rec"
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_Syntax_Embeddings.e_unit
                                              uu____1462
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_TypeChecker_NBETerm.e_unit
                                              uu____1469 in
                                          let uu____1486 =
                                            let uu____1489 =
                                              let uu____1490 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_norm_step in
                                              let uu____1495 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_norm_step in
                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                Prims.int_zero "norm"
                                                FStar_Tactics_Basic.norm
                                                uu____1490
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.norm
                                                uu____1495
                                                FStar_TypeChecker_NBETerm.e_unit in
                                            let uu____1506 =
                                              let uu____1509 =
                                                let uu____1510 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step in
                                                let uu____1515 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step in
                                                FStar_Tactics_InterpFuns.mk_tac_step_3
                                                  Prims.int_zero
                                                  "norm_term_env"
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_Embeddings.e_env
                                                  uu____1510
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                  uu____1515
                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                  FStar_Reflection_NBEEmbeddings.e_term in
                                              let uu____1526 =
                                                let uu____1529 =
                                                  let uu____1530 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step in
                                                  let uu____1535 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step in
                                                  FStar_Tactics_InterpFuns.mk_tac_step_2
                                                    Prims.int_zero
                                                    "norm_binder_type"
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1530
                                                    FStar_Reflection_Embeddings.e_binder
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1535
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                let uu____1546 =
                                                  let uu____1549 =
                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                      Prims.int_zero
                                                      "rename_to"
                                                      FStar_Tactics_Basic.rename_to
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Tactics_Basic.rename_to
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_string
                                                      FStar_Reflection_NBEEmbeddings.e_binder in
                                                  let uu____1554 =
                                                    let uu____1557 =
                                                      FStar_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "binder_retype"
                                                        FStar_Tactics_Basic.binder_retype
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.binder_retype
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_unit in
                                                    let uu____1560 =
                                                      let uu____1563 =
                                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "revert"
                                                          FStar_Tactics_Basic.revert
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.revert
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit in
                                                      let uu____1566 =
                                                        let uu____1569 =
                                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "clear_top"
                                                            FStar_Tactics_Basic.clear_top
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.clear_top
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit in
                                                        let uu____1572 =
                                                          let uu____1575 =
                                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "clear"
                                                              FStar_Tactics_Basic.clear
                                                              FStar_Reflection_Embeddings.e_binder
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.clear
                                                              FStar_Reflection_NBEEmbeddings.e_binder
                                                              FStar_TypeChecker_NBETerm.e_unit in
                                                          let uu____1578 =
                                                            let uu____1581 =
                                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "rewrite"
                                                                FStar_Tactics_Basic.rewrite
                                                                FStar_Reflection_Embeddings.e_binder
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.rewrite
                                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                                FStar_TypeChecker_NBETerm.e_unit in
                                                            let uu____1584 =
                                                              let uu____1587
                                                                =
                                                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                  Prims.int_zero
                                                                  "refine_intro"
                                                                  FStar_Tactics_Basic.refine_intro
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_Basic.refine_intro
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                  FStar_TypeChecker_NBETerm.e_unit in
                                                              let uu____1590
                                                                =
                                                                let uu____1593
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_exact"
                                                                    FStar_Tactics_Basic.t_exact
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_exact
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                let uu____1600
                                                                  =
                                                                  let uu____1603
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_apply"
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_apply
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                  let uu____1610
                                                                    =
                                                                    let uu____1613
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "apply_lemma"
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1616
                                                                    =
                                                                    let uu____1619
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_options"
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1624
                                                                    =
                                                                    let uu____1627
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tcc"
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_comp
                                                                    FStar_Tactics_Basic.tcc
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_comp in
                                                                    let uu____1630
                                                                    =
                                                                    let uu____1633
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "tc"
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1636
                                                                    =
                                                                    let uu____1639
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1642
                                                                    =
                                                                    let uu____1645
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1650
                                                                    ->
                                                                    fun
                                                                    uu____1651
                                                                    ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____1655
                                                                    =
                                                                    let uu____1658
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1663
                                                                    =
                                                                    let uu____1666
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1671
                                                                    =
                                                                    let uu____1674
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1679
                                                                    =
                                                                    let uu____1682
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "debugging"
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu____1687
                                                                    =
                                                                    let uu____1690
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dump"
                                                                    FStar_Tactics_Basic.dump
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dump
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1695
                                                                    =
                                                                    let uu____1698
                                                                    =
                                                                    let uu____1699
                                                                    =
                                                                    let uu____1712
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1712 in
                                                                    let uu____1726
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____1731
                                                                    =
                                                                    let uu____1744
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1744 in
                                                                    let uu____1758
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1699
                                                                    uu____1726
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1731
                                                                    uu____1758
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1789
                                                                    =
                                                                    let uu____1792
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1795
                                                                    =
                                                                    let uu____1798
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1801
                                                                    =
                                                                    let uu____1804
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1807
                                                                    =
                                                                    let uu____1810
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1813
                                                                    =
                                                                    let uu____1816
                                                                    =
                                                                    let uu____1817
                                                                    =
                                                                    let uu____1826
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1826 in
                                                                    let uu____1837
                                                                    =
                                                                    let uu____1846
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1846 in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1817
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1837 in
                                                                    let uu____1871
                                                                    =
                                                                    let uu____1874
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env in
                                                                    let uu____1877
                                                                    =
                                                                    let uu____1880
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view in
                                                                    let uu____1883
                                                                    =
                                                                    let uu____1886
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1889
                                                                    =
                                                                    let uu____1892
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    let uu____1895
                                                                    =
                                                                    let uu____1898
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "curms"
                                                                    FStar_Tactics_Basic.curms
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.curms
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    let uu____1901
                                                                    =
                                                                    let uu____1904
                                                                    =
                                                                    let uu____1905
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____1910
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1905
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1910
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1921
                                                                    =
                                                                    let uu____1924
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu____1929
                                                                    =
                                                                    let uu____1932
                                                                    =
                                                                    let uu____1933
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu____1940
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1933
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1940
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu____1961
                                                                    =
                                                                    let uu____1964
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_bv in
                                                                    let uu____1969
                                                                    =
                                                                    let uu____1972
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1975
                                                                    =
                                                                    let uu____1978
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe in
                                                                    let uu____1981
                                                                    =
                                                                    let uu____1984
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1987
                                                                    =
                                                                    let uu____1990
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu____1995
                                                                    =
                                                                    let uu____1998
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____2005
                                                                    ->
                                                                    fun
                                                                    uu____2006
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____2009
                                                                    =
                                                                    let uu____2012
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_one
                                                                    "lset"
                                                                    FStar_Tactics_Basic.lset
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (fun
                                                                    uu____2020
                                                                    ->
                                                                    fun
                                                                    uu____2021
                                                                    ->
                                                                    fun
                                                                    uu____2022
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    [uu____2012] in
                                                                    uu____1998
                                                                    ::
                                                                    uu____2009 in
                                                                    uu____1990
                                                                    ::
                                                                    uu____1995 in
                                                                    uu____1984
                                                                    ::
                                                                    uu____1987 in
                                                                    uu____1978
                                                                    ::
                                                                    uu____1981 in
                                                                    uu____1972
                                                                    ::
                                                                    uu____1975 in
                                                                    uu____1964
                                                                    ::
                                                                    uu____1969 in
                                                                    uu____1932
                                                                    ::
                                                                    uu____1961 in
                                                                    uu____1924
                                                                    ::
                                                                    uu____1929 in
                                                                    uu____1904
                                                                    ::
                                                                    uu____1921 in
                                                                    uu____1898
                                                                    ::
                                                                    uu____1901 in
                                                                    uu____1892
                                                                    ::
                                                                    uu____1895 in
                                                                    uu____1886
                                                                    ::
                                                                    uu____1889 in
                                                                    uu____1880
                                                                    ::
                                                                    uu____1883 in
                                                                    uu____1874
                                                                    ::
                                                                    uu____1877 in
                                                                    uu____1816
                                                                    ::
                                                                    uu____1871 in
                                                                    uu____1810
                                                                    ::
                                                                    uu____1813 in
                                                                    uu____1804
                                                                    ::
                                                                    uu____1807 in
                                                                    uu____1798
                                                                    ::
                                                                    uu____1801 in
                                                                    uu____1792
                                                                    ::
                                                                    uu____1795 in
                                                                    uu____1698
                                                                    ::
                                                                    uu____1789 in
                                                                    uu____1690
                                                                    ::
                                                                    uu____1695 in
                                                                    uu____1682
                                                                    ::
                                                                    uu____1687 in
                                                                    uu____1674
                                                                    ::
                                                                    uu____1679 in
                                                                    uu____1666
                                                                    ::
                                                                    uu____1671 in
                                                                    uu____1658
                                                                    ::
                                                                    uu____1663 in
                                                                    uu____1645
                                                                    ::
                                                                    uu____1655 in
                                                                    uu____1639
                                                                    ::
                                                                    uu____1642 in
                                                                    uu____1633
                                                                    ::
                                                                    uu____1636 in
                                                                    uu____1627
                                                                    ::
                                                                    uu____1630 in
                                                                    uu____1619
                                                                    ::
                                                                    uu____1624 in
                                                                    uu____1613
                                                                    ::
                                                                    uu____1616 in
                                                                  uu____1603
                                                                    ::
                                                                    uu____1610 in
                                                                uu____1593 ::
                                                                  uu____1600 in
                                                              uu____1587 ::
                                                                uu____1590 in
                                                            uu____1581 ::
                                                              uu____1584 in
                                                          uu____1575 ::
                                                            uu____1578 in
                                                        uu____1569 ::
                                                          uu____1572 in
                                                      uu____1563 ::
                                                        uu____1566 in
                                                    uu____1557 :: uu____1560 in
                                                  uu____1549 :: uu____1554 in
                                                uu____1529 :: uu____1546 in
                                              uu____1509 :: uu____1526 in
                                            uu____1489 :: uu____1506 in
                                          uu____1461 :: uu____1486 in
                                        uu____1455 :: uu____1458 in
                                      uu____1409 :: uu____1452 in
                                    uu____1363 :: uu____1406 in
                                  uu____1357 :: uu____1360 in
                                uu____1337 :: uu____1354 in
                              uu____1317 :: uu____1334 in
                            uu____1309 :: uu____1314 in
                          uu____1301 :: uu____1306 in
                        uu____1293 :: uu____1298 in
                      uu____1287 :: uu____1290 in
                    uu____1281 :: uu____1284 in
                  uu____1275 :: uu____1278 in
                uu____1255 :: uu____1272 in
              uu____1235 :: uu____1252 in
            uu____1229 :: uu____1232 in
          uu____1223 :: uu____1226 in
        uu____1217 :: uu____1220 in
      uu____1211 :: uu____1214 in
    FStar_All.pipe_left
      (fun uu____2033 -> FStar_Pervasives_Native.Some uu____2033) uu____1208 in
  FStar_ST.op_Colon_Equals __primitive_steps_ref uu____1203

let unembed_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('a -> 'r FStar_Tactics_Monad.tac) FStar_Pervasives_Native.option
  =
  fun ea ->
    fun er ->
      fun f ->
        fun ncb ->
          FStar_Pervasives_Native.Some
            (fun x ->
               let rng = FStar_Range.dummyRange in
               let x_tm = embed ea rng x ncb in
               let app =
                 let uu____2127 =
                   let uu____2128 = FStar_Syntax_Syntax.as_arg x_tm in
                   [uu____2128] in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2127 rng in
               unembed_tactic_0 er app ncb)
let e_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a ->
           FStar_Tactics_Types.proofstate -> 'r FStar_Tactics_Result.__result)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    fun er ->
      let em uu____2218 uu____2219 uu____2220 uu____2221 =
        failwith "Impossible: embedding tactic (1)?" in
      let un t0 w n =
        let uu____2270 = unembed_tactic_1_alt ea er t0 n in
        match uu____2270 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x ->
                  let uu____2310 = f x in FStar_Tactics_Monad.run uu____2310))
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu____2326 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb em un uu____2326
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng ->
    fun is ->
      let errs =
        FStar_List.map
          (fun imp ->
             let uu____2366 =
               let uu____2368 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____2370 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2368 uu____2370
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2366, rng)) is in
      FStar_Errors.add_errors errs; FStar_Errors.stop_if_err ()
let run_tactic_on_ps :
  'a 'b .
    FStar_Range.range ->
      FStar_Range.range ->
        'a FStar_Syntax_Embeddings.embedding ->
          'a ->
            'b FStar_Syntax_Embeddings.embedding ->
              FStar_Syntax_Syntax.term ->
                FStar_Tactics_Types.proofstate ->
                  (FStar_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_tac ->
    fun rng_goal ->
      fun e_arg ->
        fun arg ->
          fun e_res ->
            fun tactic ->
              fun ps ->
                let env = ps.FStar_Tactics_Types.main_context in
                (let uu____2447 = FStar_ST.op_Bang tacdbg in
                 if uu____2447
                 then
                   let uu____2471 = FStar_Syntax_Print.term_to_string tactic in
                   FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                     uu____2471
                 else ());
                (let uu____2476 =
                   let uu____2483 = FStar_Syntax_Embeddings.type_of e_arg in
                   let uu____2484 = FStar_Syntax_Embeddings.type_of e_res in
                   FStar_TypeChecker_TcTerm.tc_tactic uu____2483 uu____2484
                     env tactic in
                 match uu____2476 with
                 | (uu____2491, uu____2492, g) ->
                     ((let uu____2495 = FStar_ST.op_Bang tacdbg in
                       if uu____2495
                       then FStar_Util.print_string "}\n"
                       else ());
                      FStar_TypeChecker_Rel.force_trivial_guard env g;
                      FStar_Errors.stop_if_err ();
                      (let tau =
                         unembed_tactic_1 e_arg e_res tactic
                           FStar_Syntax_Embeddings.id_norm_cb in
                       FStar_ST.op_Colon_Equals
                         FStar_Reflection_Basic.env_hook
                         (FStar_Pervasives_Native.Some env);
                       (let uu____2555 =
                          FStar_Util.record_time
                            (fun uu____2567 ->
                               let uu____2568 = tau arg in
                               FStar_Tactics_Monad.run_safe uu____2568 ps) in
                        match uu____2555 with
                        | (res, ms) ->
                            ((let uu____2586 = FStar_ST.op_Bang tacdbg in
                              if uu____2586
                              then FStar_Util.print_string "}\n"
                              else ());
                             (let uu____2614 =
                                (FStar_ST.op_Bang tacdbg) ||
                                  (FStar_Options.tactics_info ()) in
                              if uu____2614
                              then
                                let uu____2638 =
                                  FStar_Syntax_Print.term_to_string tactic in
                                let uu____2640 = FStar_Util.string_of_int ms in
                                let uu____2642 =
                                  FStar_Syntax_Print.lid_to_string
                                    env.FStar_TypeChecker_Env.curmodule in
                                FStar_Util.print3
                                  "Tactic %s ran in %s ms (%s)\n" uu____2638
                                  uu____2640 uu____2642
                              else ());
                             (match res with
                              | FStar_Tactics_Result.Success (ret, ps1) ->
                                  (FStar_List.iter
                                     (fun g1 ->
                                        let uu____2660 =
                                          FStar_Tactics_Types.is_irrelevant
                                            g1 in
                                        if uu____2660
                                        then
                                          let uu____2663 =
                                            let uu____2665 =
                                              FStar_Tactics_Types.goal_env g1 in
                                            let uu____2666 =
                                              FStar_Tactics_Types.goal_witness
                                                g1 in
                                            FStar_TypeChecker_Rel.teq_nosmt_force
                                              uu____2665 uu____2666
                                              FStar_Syntax_Util.exp_unit in
                                          (if uu____2663
                                           then ()
                                           else
                                             (let uu____2670 =
                                                let uu____2672 =
                                                  let uu____2674 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1 in
                                                  FStar_Syntax_Print.term_to_string
                                                    uu____2674 in
                                                FStar_Util.format1
                                                  "Irrelevant tactic witness does not unify with (): %s"
                                                  uu____2672 in
                                              failwith uu____2670))
                                        else ())
                                     (FStar_List.append
                                        ps1.FStar_Tactics_Types.goals
                                        ps1.FStar_Tactics_Types.smt_goals);
                                   (let uu____2679 = FStar_ST.op_Bang tacdbg in
                                    if uu____2679
                                    then
                                      let uu____2703 =
                                        FStar_Common.string_of_list
                                          (fun imp ->
                                             FStar_Syntax_Print.ctx_uvar_to_string
                                               imp.FStar_TypeChecker_Common.imp_uvar)
                                          ps1.FStar_Tactics_Types.all_implicits in
                                      FStar_Util.print1
                                        "About to check tactic implicits: %s\n"
                                        uu____2703
                                    else ());
                                   (let g1 =
                                      let uu___232_2711 =
                                        FStar_TypeChecker_Env.trivial_guard in
                                      {
                                        FStar_TypeChecker_Common.guard_f =
                                          (uu___232_2711.FStar_TypeChecker_Common.guard_f);
                                        FStar_TypeChecker_Common.deferred_to_tac
                                          =
                                          (uu___232_2711.FStar_TypeChecker_Common.deferred_to_tac);
                                        FStar_TypeChecker_Common.deferred =
                                          (uu___232_2711.FStar_TypeChecker_Common.deferred);
                                        FStar_TypeChecker_Common.univ_ineqs =
                                          (uu___232_2711.FStar_TypeChecker_Common.univ_ineqs);
                                        FStar_TypeChecker_Common.implicits =
                                          (ps1.FStar_Tactics_Types.all_implicits)
                                      } in
                                    let g2 =
                                      FStar_TypeChecker_Rel.solve_deferred_constraints
                                        env g1 in
                                    (let uu____2714 = FStar_ST.op_Bang tacdbg in
                                     if uu____2714
                                     then
                                       let uu____2738 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length
                                              ps1.FStar_Tactics_Types.all_implicits) in
                                       let uu____2740 =
                                         FStar_Common.string_of_list
                                           (fun imp ->
                                              FStar_Syntax_Print.ctx_uvar_to_string
                                                imp.FStar_TypeChecker_Common.imp_uvar)
                                           ps1.FStar_Tactics_Types.all_implicits in
                                       FStar_Util.print2
                                         "Checked %s implicits (1): %s\n"
                                         uu____2738 uu____2740
                                     else ());
                                    (let g3 =
                                       FStar_TypeChecker_Rel.resolve_implicits_tac
                                         env g2 in
                                     (let uu____2749 =
                                        FStar_ST.op_Bang tacdbg in
                                      if uu____2749
                                      then
                                        let uu____2773 =
                                          FStar_Util.string_of_int
                                            (FStar_List.length
                                               ps1.FStar_Tactics_Types.all_implicits) in
                                        let uu____2775 =
                                          FStar_Common.string_of_list
                                            (fun imp ->
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 imp.FStar_TypeChecker_Common.imp_uvar)
                                            ps1.FStar_Tactics_Types.all_implicits in
                                        FStar_Util.print2
                                          "Checked %s implicits (2): %s\n"
                                          uu____2773 uu____2775
                                      else ());
                                     report_implicits rng_goal
                                       g3.FStar_TypeChecker_Common.implicits;
                                     (let uu____2784 =
                                        FStar_ST.op_Bang tacdbg in
                                      if uu____2784
                                      then
                                        let uu____2808 =
                                          let uu____2809 =
                                            FStar_TypeChecker_Cfg.psc_subst
                                              ps1.FStar_Tactics_Types.psc in
                                          FStar_Tactics_Types.subst_proof_state
                                            uu____2809 ps1 in
                                        FStar_Tactics_Printing.do_dump_proofstate
                                          uu____2808 "at the finish line"
                                      else ());
                                     ((FStar_List.append
                                         ps1.FStar_Tactics_Types.goals
                                         ps1.FStar_Tactics_Types.smt_goals),
                                       ret))))
                              | FStar_Tactics_Result.Failed (e, ps1) ->
                                  ((let uu____2818 =
                                      let uu____2819 =
                                        FStar_TypeChecker_Cfg.psc_subst
                                          ps1.FStar_Tactics_Types.psc in
                                      FStar_Tactics_Types.subst_proof_state
                                        uu____2819 ps1 in
                                    FStar_Tactics_Printing.do_dump_proofstate
                                      uu____2818 "at the time of failure");
                                   (let texn_to_string e1 =
                                      match e1 with
                                      | FStar_Tactics_Types.TacticFailure s
                                          -> s
                                      | FStar_Tactics_Types.EExn t ->
                                          let uu____2832 =
                                            FStar_Syntax_Print.term_to_string
                                              t in
                                          Prims.op_Hat "uncaught exception: "
                                            uu____2832
                                      | e2 -> FStar_Exn.raise e2 in
                                    let uu____2837 =
                                      let uu____2843 =
                                        let uu____2845 = texn_to_string e in
                                        FStar_Util.format1
                                          "user tactic failed: %s" uu____2845 in
                                      (FStar_Errors.Fatal_UserTacticFailure,
                                        uu____2843) in
                                    FStar_Errors.raise_error uu____2837
                                      ps1.FStar_Tactics_Types.entry_range))))))))