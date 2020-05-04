open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let unembed :
  'uuuuuu14 .
    'uuuuuu14 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuuu14 FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun a  ->
      fun norm_cb  ->
        let uu____38 = FStar_Syntax_Embeddings.unembed ea a  in
        uu____38 true norm_cb
  
let embed :
  'uuuuuu57 .
    'uuuuuu57 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuuu57 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea  ->
    fun r  ->
      fun x  ->
        fun norm_cb  ->
          let uu____84 = FStar_Syntax_Embeddings.embed ea x  in
          uu____84 r FStar_Pervasives_Native.None norm_cb
  
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____100  ->
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
          (fun _cb  ->
             FStar_TypeChecker_NBETerm.dummy_interp
               s.FStar_Tactics_Native.name)
      }  in
    let uu____113 = FStar_Tactics_Native.list_all ()  in
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
  fun uarity  ->
    fun nm  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            fun nf  ->
              fun ena  ->
                fun enr  ->
                  let uu___19_215 =
                    FStar_Tactics_InterpFuns.mk_total_step_1 uarity nm f ea
                      er nf ena enr
                     in
                  let uu____216 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
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
  fun uarity  ->
    fun nm  ->
      fun f  ->
        fun ea  ->
          fun er  ->
            fun nf  ->
              fun ena  ->
                fun enr  ->
                  let uu___29_327 =
                    FStar_Tactics_InterpFuns.mk_total_step_1_psc uarity nm f
                      ea er nf ena enr
                     in
                  let uu____328 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm)
                     in
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
  fun uarity  ->
    fun nm  ->
      fun f  ->
        fun ea  ->
          fun eb  ->
            fun er  ->
              fun nf  ->
                fun ena  ->
                  fun enb  ->
                    fun enr  ->
                      let uu___41_467 =
                        FStar_Tactics_InterpFuns.mk_total_step_2 uarity nm f
                          ea eb er nf ena enb enr
                         in
                      let uu____468 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm)
                         in
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
  fun uu____490  ->
    let uu____493 =
      let uu____496 = FStar_ST.op_Bang __primitive_steps_ref  in
      FStar_Util.must uu____496  in
    let uu____530 = native_tactics_steps ()  in
    FStar_List.append uu____493 uu____530
  
let unembed_tactic_0 :
  'b .
    'b FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'b FStar_Tactics_Monad.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      fun ncb  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state  ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
             let embedded_tac_b1 = FStar_Syntax_Util.mk_reify embedded_tac_b
                in
             let tm =
               let uu____583 =
                 let uu____584 =
                   let uu____593 =
                     embed FStar_Tactics_Embedding.e_proofstate rng
                       proof_state ncb
                      in
                   FStar_Syntax_Syntax.as_arg uu____593  in
                 [uu____584]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____583 rng
                in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____634 = FStar_Options.tactics_nbe ()  in
               if uu____634
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____656 = primitive_steps ()  in
               norm_f uu____656 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____664 = FStar_Tactics_Embedding.e_result eb  in
               unembed uu____664 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1,ps)) ->
                 let uu____677 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____677
                   (fun uu____681  -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____686 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____686
                   (fun uu____690  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____693 =
                   let uu____699 =
                     let uu____701 = FStar_Syntax_Print.term_to_string result
                        in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____701
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____699)  in
                 FStar_Errors.raise_error uu____693
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)
  
let unembed_tactic_nbe_0 :
  'b .
    'b FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'b FStar_Tactics_Monad.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun proof_state  ->
             let result =
               let uu____746 =
                 let uu____747 =
                   let uu____752 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____752  in
                 [uu____747]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____746
                in
             let res =
               let uu____766 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____766 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1,ps)) ->
                 let uu____779 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____779
                   (fun uu____783  -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____788 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____788
                   (fun uu____792  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____795 =
                   let uu____801 =
                     let uu____803 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____803
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____801)  in
                 FStar_Errors.raise_error uu____795
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)
  
let unembed_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb -> 'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          fun x  ->
            let rng = FStar_Range.dummyRange  in
            let x_tm = embed ea rng x ncb  in
            let app =
              let uu____863 =
                let uu____864 = FStar_Syntax_Syntax.as_arg x_tm  in
                [uu____864]  in
              FStar_Syntax_Syntax.mk_Tm_app f uu____863 rng  in
            unembed_tactic_0 er app ncb
  
let unembed_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'a -> 'r FStar_Tactics_Monad.tac
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          fun x  ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
            let app =
              let uu____940 =
                let uu____941 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____941]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____940  in
            unembed_tactic_nbe_0 er cb app
  
let e_tactic_thunk :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____973 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____980  ->
         fun uu____981  ->
           fun uu____982  ->
             fun uu____983  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____997 =
               let uu____1000 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____1000 ()  in
             FStar_Pervasives_Native.Some uu____997) uu____973
  
let e_tactic_nbe_thunk :
  'r .
    'r FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____1028 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____1034  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____1043 =
             let uu____1046 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____1046 ()  in
           FStar_Pervasives_Native.Some uu____1043)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____1028
  
let e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____1091 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____1101  ->
           fun uu____1102  ->
             fun uu____1103  ->
               fun uu____1104  ->
                 failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____1120 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____1120) uu____1091
  
let e_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____1168 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____1177  ->
             failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____1188 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____1188)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____1168
  
let (uu___143 : unit) =
  let uu____1201 =
    let uu____1206 =
      let uu____1209 =
        mk_total_step_1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____1212 =
        let uu____1215 =
          mk_total_step_2' Prims.int_zero "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe
           in
        let uu____1218 =
          let uu____1221 =
            mk_total_step_1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____1224 =
            let uu____1227 =
              mk_total_step_1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____1230 =
              let uu____1233 =
                let uu____1234 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____1239 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mk_total_step_1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____1234
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____1239
                 in
              let uu____1250 =
                let uu____1253 =
                  let uu____1254 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____1259 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mk_total_step_1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____1254
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____1259
                   in
                let uu____1270 =
                  let uu____1273 =
                    mk_total_step_1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____1276 =
                    let uu____1279 =
                      mk_total_step_1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____1282 =
                      let uu____1285 =
                        mk_total_step_1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____1288 =
                        let uu____1291 =
                          mk_total_step_1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____1296 =
                          let uu____1299 =
                            mk_total_step_1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____1304 =
                            let uu____1307 =
                              mk_total_step_2' Prims.int_zero "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe
                               in
                            let uu____1312 =
                              let uu____1315 =
                                let uu____1316 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Tactics_Embedding.e_goal
                                   in
                                let uu____1321 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_Tactics_Embedding.e_goal_nbe
                                   in
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "set_goals"
                                  FStar_Tactics_Monad.set_goals uu____1316
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Monad.set_goals uu____1321
                                  FStar_TypeChecker_NBETerm.e_unit
                                 in
                              let uu____1332 =
                                let uu____1335 =
                                  let uu____1336 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____1341 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_smt_goals"
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1336 FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1341
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____1352 =
                                  let uu____1355 =
                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "trivial"
                                      FStar_Tactics_Basic.trivial
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.trivial
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____1358 =
                                    let uu____1361 =
                                      let uu____1362 =
                                        e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any
                                         in
                                      let uu____1367 =
                                        FStar_Syntax_Embeddings.e_either
                                          FStar_Tactics_Embedding.e_exn
                                          FStar_Syntax_Embeddings.e_any
                                         in
                                      let uu____1374 =
                                        e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any
                                         in
                                      let uu____1379 =
                                        FStar_TypeChecker_NBETerm.e_either
                                          FStar_Tactics_Embedding.e_exn_nbe
                                          FStar_TypeChecker_NBETerm.e_any
                                         in
                                      FStar_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "catch"
                                        (fun uu____1401  ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_Syntax_Embeddings.e_any
                                        uu____1362 uu____1367
                                        (fun uu____1403  ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu____1374 uu____1379
                                       in
                                    let uu____1404 =
                                      let uu____1407 =
                                        let uu____1408 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____1413 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____1420 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____1425 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mk_tac_step_2
                                          Prims.int_one "recover"
                                          (fun uu____1447  ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____1408 uu____1413
                                          (fun uu____1449  ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____1420 uu____1425
                                         in
                                      let uu____1450 =
                                        let uu____1453 =
                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intro"
                                            FStar_Tactics_Basic.intro
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Tactics_Basic.intro
                                            FStar_TypeChecker_NBETerm.e_unit
                                            FStar_Reflection_NBEEmbeddings.e_binder
                                           in
                                        let uu____1456 =
                                          let uu____1459 =
                                            let uu____1460 =
                                              FStar_Syntax_Embeddings.e_tuple2
                                                FStar_Reflection_Embeddings.e_binder
                                                FStar_Reflection_Embeddings.e_binder
                                               in
                                            let uu____1467 =
                                              FStar_TypeChecker_NBETerm.e_tuple2
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                               in
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "intro_rec"
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_Syntax_Embeddings.e_unit
                                              uu____1460
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_TypeChecker_NBETerm.e_unit
                                              uu____1467
                                             in
                                          let uu____1484 =
                                            let uu____1487 =
                                              let uu____1488 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_norm_step
                                                 in
                                              let uu____1493 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_norm_step
                                                 in
                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                Prims.int_zero "norm"
                                                FStar_Tactics_Basic.norm
                                                uu____1488
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.norm
                                                uu____1493
                                                FStar_TypeChecker_NBETerm.e_unit
                                               in
                                            let uu____1504 =
                                              let uu____1507 =
                                                let uu____1508 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____1513 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mk_tac_step_3
                                                  Prims.int_zero
                                                  "norm_term_env"
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_Embeddings.e_env
                                                  uu____1508
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                  uu____1513
                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                 in
                                              let uu____1524 =
                                                let uu____1527 =
                                                  let uu____1528 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1533 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mk_tac_step_2
                                                    Prims.int_zero
                                                    "norm_binder_type"
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1528
                                                    FStar_Reflection_Embeddings.e_binder
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1533
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                   in
                                                let uu____1544 =
                                                  let uu____1547 =
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
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                     in
                                                  let uu____1552 =
                                                    let uu____1555 =
                                                      FStar_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "binder_retype"
                                                        FStar_Tactics_Basic.binder_retype
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.binder_retype
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                       in
                                                    let uu____1558 =
                                                      let uu____1561 =
                                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "revert"
                                                          FStar_Tactics_Basic.revert
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.revert
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                         in
                                                      let uu____1564 =
                                                        let uu____1567 =
                                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "clear_top"
                                                            FStar_Tactics_Basic.clear_top
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.clear_top
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                           in
                                                        let uu____1570 =
                                                          let uu____1573 =
                                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "clear"
                                                              FStar_Tactics_Basic.clear
                                                              FStar_Reflection_Embeddings.e_binder
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.clear
                                                              FStar_Reflection_NBEEmbeddings.e_binder
                                                              FStar_TypeChecker_NBETerm.e_unit
                                                             in
                                                          let uu____1576 =
                                                            let uu____1579 =
                                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "rewrite"
                                                                FStar_Tactics_Basic.rewrite
                                                                FStar_Reflection_Embeddings.e_binder
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.rewrite
                                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____1582 =
                                                              let uu____1585
                                                                =
                                                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                  Prims.int_zero
                                                                  "refine_intro"
                                                                  FStar_Tactics_Basic.refine_intro
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_Basic.refine_intro
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                 in
                                                              let uu____1588
                                                                =
                                                                let uu____1591
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
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                   in
                                                                let uu____1598
                                                                  =
                                                                  let uu____1601
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
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                  let uu____1608
                                                                    =
                                                                    let uu____1611
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "apply_lemma"
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.apply_lemma
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1614
                                                                    =
                                                                    let uu____1617
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_options"
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1622
                                                                    =
                                                                    let uu____1625
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
                                                                    FStar_Reflection_NBEEmbeddings.e_comp
                                                                     in
                                                                    let uu____1628
                                                                    =
                                                                    let uu____1631
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
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1634
                                                                    =
                                                                    let uu____1637
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1640
                                                                    =
                                                                    let uu____1643
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1648
                                                                     ->
                                                                    fun
                                                                    uu____1649
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1653
                                                                    =
                                                                    let uu____1656
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1661
                                                                    =
                                                                    let uu____1664
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1669
                                                                    =
                                                                    let uu____1672
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1677
                                                                    =
                                                                    let uu____1680
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "debugging"
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.debugging
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1685
                                                                    =
                                                                    let uu____1688
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dump"
                                                                    FStar_Tactics_Basic.dump
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dump
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1693
                                                                    =
                                                                    let uu____1696
                                                                    =
                                                                    let uu____1697
                                                                    =
                                                                    let uu____1710
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1710
                                                                     in
                                                                    let uu____1724
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1729
                                                                    =
                                                                    let uu____1742
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1742
                                                                     in
                                                                    let uu____1756
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1697
                                                                    uu____1724
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1729
                                                                    uu____1756
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1787
                                                                    =
                                                                    let uu____1790
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1793
                                                                    =
                                                                    let uu____1796
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1799
                                                                    =
                                                                    let uu____1802
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "tadmit_t"
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit_t
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1805
                                                                    =
                                                                    let uu____1808
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "join"
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1811
                                                                    =
                                                                    let uu____1814
                                                                    =
                                                                    let uu____1815
                                                                    =
                                                                    let uu____1824
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1824
                                                                     in
                                                                    let uu____1835
                                                                    =
                                                                    let uu____1844
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1844
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1815
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1835
                                                                     in
                                                                    let uu____1869
                                                                    =
                                                                    let uu____1872
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                     in
                                                                    let uu____1875
                                                                    =
                                                                    let uu____1878
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                     in
                                                                    let uu____1881
                                                                    =
                                                                    let uu____1884
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1887
                                                                    =
                                                                    let uu____1890
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1893
                                                                    =
                                                                    let uu____1896
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "curms"
                                                                    FStar_Tactics_Basic.curms
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.curms
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1899
                                                                    =
                                                                    let uu____1902
                                                                    =
                                                                    let uu____1903
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1908
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1903
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1908
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1919
                                                                    =
                                                                    let uu____1922
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
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1927
                                                                    =
                                                                    let uu____1930
                                                                    =
                                                                    let uu____1931
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1938
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1931
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1938
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1959
                                                                    =
                                                                    let uu____1962
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
                                                                    FStar_Reflection_NBEEmbeddings.e_bv
                                                                     in
                                                                    let uu____1967
                                                                    =
                                                                    let uu____1970
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1973
                                                                    =
                                                                    let uu____1976
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                     in
                                                                    let uu____1979
                                                                    =
                                                                    let uu____1982
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1985
                                                                    =
                                                                    let uu____1988
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1993
                                                                    =
                                                                    let uu____1996
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____2003
                                                                     ->
                                                                    fun
                                                                    uu____2004
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____2007
                                                                    =
                                                                    let uu____2010
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
                                                                    uu____2018
                                                                     ->
                                                                    fun
                                                                    uu____2019
                                                                     ->
                                                                    fun
                                                                    uu____2020
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____2010]
                                                                     in
                                                                    uu____1996
                                                                    ::
                                                                    uu____2007
                                                                     in
                                                                    uu____1988
                                                                    ::
                                                                    uu____1993
                                                                     in
                                                                    uu____1982
                                                                    ::
                                                                    uu____1985
                                                                     in
                                                                    uu____1976
                                                                    ::
                                                                    uu____1979
                                                                     in
                                                                    uu____1970
                                                                    ::
                                                                    uu____1973
                                                                     in
                                                                    uu____1962
                                                                    ::
                                                                    uu____1967
                                                                     in
                                                                    uu____1930
                                                                    ::
                                                                    uu____1959
                                                                     in
                                                                    uu____1922
                                                                    ::
                                                                    uu____1927
                                                                     in
                                                                    uu____1902
                                                                    ::
                                                                    uu____1919
                                                                     in
                                                                    uu____1896
                                                                    ::
                                                                    uu____1899
                                                                     in
                                                                    uu____1890
                                                                    ::
                                                                    uu____1893
                                                                     in
                                                                    uu____1884
                                                                    ::
                                                                    uu____1887
                                                                     in
                                                                    uu____1878
                                                                    ::
                                                                    uu____1881
                                                                     in
                                                                    uu____1872
                                                                    ::
                                                                    uu____1875
                                                                     in
                                                                    uu____1814
                                                                    ::
                                                                    uu____1869
                                                                     in
                                                                    uu____1808
                                                                    ::
                                                                    uu____1811
                                                                     in
                                                                    uu____1802
                                                                    ::
                                                                    uu____1805
                                                                     in
                                                                    uu____1796
                                                                    ::
                                                                    uu____1799
                                                                     in
                                                                    uu____1790
                                                                    ::
                                                                    uu____1793
                                                                     in
                                                                    uu____1696
                                                                    ::
                                                                    uu____1787
                                                                     in
                                                                    uu____1688
                                                                    ::
                                                                    uu____1693
                                                                     in
                                                                    uu____1680
                                                                    ::
                                                                    uu____1685
                                                                     in
                                                                    uu____1672
                                                                    ::
                                                                    uu____1677
                                                                     in
                                                                    uu____1664
                                                                    ::
                                                                    uu____1669
                                                                     in
                                                                    uu____1656
                                                                    ::
                                                                    uu____1661
                                                                     in
                                                                    uu____1643
                                                                    ::
                                                                    uu____1653
                                                                     in
                                                                    uu____1637
                                                                    ::
                                                                    uu____1640
                                                                     in
                                                                    uu____1631
                                                                    ::
                                                                    uu____1634
                                                                     in
                                                                    uu____1625
                                                                    ::
                                                                    uu____1628
                                                                     in
                                                                    uu____1617
                                                                    ::
                                                                    uu____1622
                                                                     in
                                                                    uu____1611
                                                                    ::
                                                                    uu____1614
                                                                     in
                                                                  uu____1601
                                                                    ::
                                                                    uu____1608
                                                                   in
                                                                uu____1591 ::
                                                                  uu____1598
                                                                 in
                                                              uu____1585 ::
                                                                uu____1588
                                                               in
                                                            uu____1579 ::
                                                              uu____1582
                                                             in
                                                          uu____1573 ::
                                                            uu____1576
                                                           in
                                                        uu____1567 ::
                                                          uu____1570
                                                         in
                                                      uu____1561 ::
                                                        uu____1564
                                                       in
                                                    uu____1555 :: uu____1558
                                                     in
                                                  uu____1547 :: uu____1552
                                                   in
                                                uu____1527 :: uu____1544  in
                                              uu____1507 :: uu____1524  in
                                            uu____1487 :: uu____1504  in
                                          uu____1459 :: uu____1484  in
                                        uu____1453 :: uu____1456  in
                                      uu____1407 :: uu____1450  in
                                    uu____1361 :: uu____1404  in
                                  uu____1355 :: uu____1358  in
                                uu____1335 :: uu____1352  in
                              uu____1315 :: uu____1332  in
                            uu____1307 :: uu____1312  in
                          uu____1299 :: uu____1304  in
                        uu____1291 :: uu____1296  in
                      uu____1285 :: uu____1288  in
                    uu____1279 :: uu____1282  in
                  uu____1273 :: uu____1276  in
                uu____1253 :: uu____1270  in
              uu____1233 :: uu____1250  in
            uu____1227 :: uu____1230  in
          uu____1221 :: uu____1224  in
        uu____1215 :: uu____1218  in
      uu____1209 :: uu____1212  in
    FStar_All.pipe_left
      (fun uu____2031  -> FStar_Pervasives_Native.Some uu____2031) uu____1206
     in
  FStar_ST.op_Colon_Equals __primitive_steps_ref uu____1201 

let unembed_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('a -> 'r FStar_Tactics_Monad.tac) FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let rng = FStar_Range.dummyRange  in
               let x_tm = embed ea rng x ncb  in
               let app =
                 let uu____2125 =
                   let uu____2126 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____2126]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____2125 rng  in
               unembed_tactic_0 er app ncb)
  
let e_tactic_1_alt :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a ->
           FStar_Tactics_Types.proofstate -> 'r FStar_Tactics_Result.__result)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let em uu____2216 uu____2217 uu____2218 uu____2219 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n =
        let uu____2268 = unembed_tactic_1_alt ea er t0 n  in
        match uu____2268 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2308 = f x  in FStar_Tactics_Monad.run uu____2308))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2324 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2324
  
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2364 =
               let uu____2366 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2368 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2366 uu____2368
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2364, rng)) is
         in
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
  fun rng_tac  ->
    fun rng_goal  ->
      fun e_arg  ->
        fun arg  ->
          fun e_res  ->
            fun tactic  ->
              fun ps  ->
                let env = ps.FStar_Tactics_Types.main_context  in
                (let uu____2445 = FStar_ST.op_Bang tacdbg  in
                 if uu____2445
                 then
                   let uu____2469 = FStar_Syntax_Print.term_to_string tactic
                      in
                   FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                     uu____2469
                 else ());
                (let uu____2474 =
                   let uu____2481 = FStar_Syntax_Embeddings.type_of e_arg  in
                   let uu____2482 = FStar_Syntax_Embeddings.type_of e_res  in
                   FStar_TypeChecker_TcTerm.tc_tactic uu____2481 uu____2482
                     env tactic
                    in
                 match uu____2474 with
                 | (uu____2489,uu____2490,g) ->
                     ((let uu____2493 = FStar_ST.op_Bang tacdbg  in
                       if uu____2493
                       then FStar_Util.print_string "}\n"
                       else ());
                      FStar_TypeChecker_Rel.force_trivial_guard env g;
                      FStar_Errors.stop_if_err ();
                      (let tau =
                         unembed_tactic_1 e_arg e_res tactic
                           FStar_Syntax_Embeddings.id_norm_cb
                          in
                       FStar_ST.op_Colon_Equals
                         FStar_Reflection_Basic.env_hook
                         (FStar_Pervasives_Native.Some env);
                       (let uu____2553 =
                          FStar_Util.record_time
                            (fun uu____2565  ->
                               let uu____2566 = tau arg  in
                               FStar_Tactics_Monad.run_safe uu____2566 ps)
                           in
                        match uu____2553 with
                        | (res,ms) ->
                            ((let uu____2584 = FStar_ST.op_Bang tacdbg  in
                              if uu____2584
                              then FStar_Util.print_string "}\n"
                              else ());
                             (let uu____2612 =
                                (FStar_ST.op_Bang tacdbg) ||
                                  (FStar_Options.tactics_info ())
                                 in
                              if uu____2612
                              then
                                let uu____2636 =
                                  FStar_Syntax_Print.term_to_string tactic
                                   in
                                let uu____2638 = FStar_Util.string_of_int ms
                                   in
                                let uu____2640 =
                                  FStar_Syntax_Print.lid_to_string
                                    env.FStar_TypeChecker_Env.curmodule
                                   in
                                FStar_Util.print3
                                  "Tactic %s ran in %s ms (%s)\n" uu____2636
                                  uu____2638 uu____2640
                              else ());
                             (match res with
                              | FStar_Tactics_Result.Success (ret,ps1) ->
                                  (FStar_List.iter
                                     (fun g1  ->
                                        let uu____2658 =
                                          FStar_Tactics_Types.is_irrelevant
                                            g1
                                           in
                                        if uu____2658
                                        then
                                          let uu____2661 =
                                            let uu____2663 =
                                              FStar_Tactics_Types.goal_env g1
                                               in
                                            let uu____2664 =
                                              FStar_Tactics_Types.goal_witness
                                                g1
                                               in
                                            FStar_TypeChecker_Rel.teq_nosmt_force
                                              uu____2663 uu____2664
                                              FStar_Syntax_Util.exp_unit
                                             in
                                          (if uu____2661
                                           then ()
                                           else
                                             (let uu____2668 =
                                                let uu____2670 =
                                                  let uu____2672 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_Syntax_Print.term_to_string
                                                    uu____2672
                                                   in
                                                FStar_Util.format1
                                                  "Irrelevant tactic witness does not unify with (): %s"
                                                  uu____2670
                                                 in
                                              failwith uu____2668))
                                        else ())
                                     (FStar_List.append
                                        ps1.FStar_Tactics_Types.goals
                                        ps1.FStar_Tactics_Types.smt_goals);
                                   (let uu____2677 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____2677
                                    then
                                      let uu____2701 =
                                        FStar_Common.string_of_list
                                          (fun imp  ->
                                             FStar_Syntax_Print.ctx_uvar_to_string
                                               imp.FStar_TypeChecker_Common.imp_uvar)
                                          ps1.FStar_Tactics_Types.all_implicits
                                         in
                                      FStar_Util.print1
                                        "About to check tactic implicits: %s\n"
                                        uu____2701
                                    else ());
                                   (let g1 =
                                      let uu___232_2709 =
                                        FStar_TypeChecker_Env.trivial_guard
                                         in
                                      {
                                        FStar_TypeChecker_Common.guard_f =
                                          (uu___232_2709.FStar_TypeChecker_Common.guard_f);
                                        FStar_TypeChecker_Common.deferred =
                                          (uu___232_2709.FStar_TypeChecker_Common.deferred);
                                        FStar_TypeChecker_Common.univ_ineqs =
                                          (uu___232_2709.FStar_TypeChecker_Common.univ_ineqs);
                                        FStar_TypeChecker_Common.implicits =
                                          (ps1.FStar_Tactics_Types.all_implicits)
                                      }  in
                                    let g2 =
                                      FStar_TypeChecker_Rel.solve_deferred_constraints
                                        env g1
                                       in
                                    (let uu____2712 = FStar_ST.op_Bang tacdbg
                                        in
                                     if uu____2712
                                     then
                                       let uu____2736 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length
                                              ps1.FStar_Tactics_Types.all_implicits)
                                          in
                                       let uu____2738 =
                                         FStar_Common.string_of_list
                                           (fun imp  ->
                                              FStar_Syntax_Print.ctx_uvar_to_string
                                                imp.FStar_TypeChecker_Common.imp_uvar)
                                           ps1.FStar_Tactics_Types.all_implicits
                                          in
                                       FStar_Util.print2
                                         "Checked %s implicits (1): %s\n"
                                         uu____2736 uu____2738
                                     else ());
                                    (let g3 =
                                       FStar_TypeChecker_Rel.resolve_implicits_tac
                                         env g2
                                        in
                                     (let uu____2747 =
                                        FStar_ST.op_Bang tacdbg  in
                                      if uu____2747
                                      then
                                        let uu____2771 =
                                          FStar_Util.string_of_int
                                            (FStar_List.length
                                               ps1.FStar_Tactics_Types.all_implicits)
                                           in
                                        let uu____2773 =
                                          FStar_Common.string_of_list
                                            (fun imp  ->
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 imp.FStar_TypeChecker_Common.imp_uvar)
                                            ps1.FStar_Tactics_Types.all_implicits
                                           in
                                        FStar_Util.print2
                                          "Checked %s implicits (2): %s\n"
                                          uu____2771 uu____2773
                                      else ());
                                     report_implicits rng_goal
                                       g3.FStar_TypeChecker_Common.implicits;
                                     (let uu____2782 =
                                        FStar_ST.op_Bang tacdbg  in
                                      if uu____2782
                                      then
                                        let uu____2806 =
                                          let uu____2807 =
                                            FStar_TypeChecker_Cfg.psc_subst
                                              ps1.FStar_Tactics_Types.psc
                                             in
                                          FStar_Tactics_Types.subst_proof_state
                                            uu____2807 ps1
                                           in
                                        FStar_Tactics_Printing.do_dump_proofstate
                                          uu____2806 "at the finish line"
                                      else ());
                                     ((FStar_List.append
                                         ps1.FStar_Tactics_Types.goals
                                         ps1.FStar_Tactics_Types.smt_goals),
                                       ret))))
                              | FStar_Tactics_Result.Failed (e,ps1) ->
                                  ((let uu____2816 =
                                      let uu____2817 =
                                        FStar_TypeChecker_Cfg.psc_subst
                                          ps1.FStar_Tactics_Types.psc
                                         in
                                      FStar_Tactics_Types.subst_proof_state
                                        uu____2817 ps1
                                       in
                                    FStar_Tactics_Printing.do_dump_proofstate
                                      uu____2816 "at the time of failure");
                                   (let texn_to_string e1 =
                                      match e1 with
                                      | FStar_Tactics_Types.TacticFailure s
                                          -> s
                                      | FStar_Tactics_Types.EExn t ->
                                          let uu____2830 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat "uncaught exception: "
                                            uu____2830
                                      | e2 -> FStar_Exn.raise e2  in
                                    let uu____2835 =
                                      let uu____2841 =
                                        let uu____2843 = texn_to_string e  in
                                        FStar_Util.format1
                                          "user tactic failed: %s" uu____2843
                                         in
                                      (FStar_Errors.Fatal_UserTacticFailure,
                                        uu____2841)
                                       in
                                    FStar_Errors.raise_error uu____2835
                                      ps1.FStar_Tactics_Types.entry_range))))))))
  