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
               let uu____585 =
                 let uu____590 =
                   let uu____591 =
                     let uu____600 =
                       embed FStar_Tactics_Embedding.e_proofstate rng
                         proof_state ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____600  in
                   [uu____591]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____590  in
               uu____585 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____641 = FStar_Options.tactics_nbe ()  in
               if uu____641
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             let result =
               let uu____663 = primitive_steps ()  in
               norm_f uu____663 steps
                 proof_state.FStar_Tactics_Types.main_context tm
                in
             let res =
               let uu____671 = FStar_Tactics_Embedding.e_result eb  in
               unembed uu____671 result ncb  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1,ps)) ->
                 let uu____684 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____684
                   (fun uu____688  -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____693 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____693
                   (fun uu____697  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____700 =
                   let uu____706 =
                     let uu____708 = FStar_Syntax_Print.term_to_string result
                        in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____708
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____706)  in
                 FStar_Errors.raise_error uu____700
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
               let uu____753 =
                 let uu____754 =
                   let uu____759 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____759  in
                 [uu____754]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____753
                in
             let res =
               let uu____773 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____773 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1,ps)) ->
                 let uu____786 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____786
                   (fun uu____790  -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e,ps)) ->
                 let uu____795 = FStar_Tactics_Monad.set ps  in
                 FStar_Tactics_Monad.bind uu____795
                   (fun uu____799  -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None  ->
                 let uu____802 =
                   let uu____808 =
                     let uu____810 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____810
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____808)  in
                 FStar_Errors.raise_error uu____802
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
              let uu____872 =
                let uu____877 =
                  let uu____878 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____878]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____877  in
              uu____872 FStar_Pervasives_Native.None rng  in
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
              let uu____954 =
                let uu____955 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____955]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____954  in
            unembed_tactic_nbe_0 er cb app
  
let e_tactic_thunk :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____987 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____994  ->
         fun uu____995  ->
           fun uu____996  ->
             fun uu____997  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____1011 =
               let uu____1014 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____1014 ()  in
             FStar_Pervasives_Native.Some uu____1011) uu____987
  
let e_tactic_nbe_thunk :
  'r .
    'r FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____1042 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____1048  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____1057 =
             let uu____1060 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____1060 ()  in
           FStar_Pervasives_Native.Some uu____1057)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____1042
  
let e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____1105 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____1115  ->
           fun uu____1116  ->
             fun uu____1117  ->
               fun uu____1118  ->
                 failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____1134 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____1134) uu____1105
  
let e_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____1182 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____1191  ->
             failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____1202 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____1202)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____1182
  
let (uu___143 : unit) =
  let uu____1215 =
    let uu____1220 =
      let uu____1223 =
        mk_total_step_1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____1226 =
        let uu____1229 =
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
        let uu____1232 =
          let uu____1235 =
            mk_total_step_1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____1238 =
            let uu____1241 =
              mk_total_step_1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____1244 =
              let uu____1247 =
                let uu____1248 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____1253 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mk_total_step_1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____1248
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____1253
                 in
              let uu____1264 =
                let uu____1267 =
                  let uu____1268 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____1273 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mk_total_step_1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____1268
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____1273
                   in
                let uu____1284 =
                  let uu____1287 =
                    mk_total_step_1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____1290 =
                    let uu____1293 =
                      mk_total_step_1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____1296 =
                      let uu____1299 =
                        mk_total_step_1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____1302 =
                        let uu____1305 =
                          mk_total_step_1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____1310 =
                          let uu____1313 =
                            mk_total_step_1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string
                             in
                          let uu____1318 =
                            let uu____1321 =
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
                            let uu____1326 =
                              let uu____1329 =
                                let uu____1330 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Tactics_Embedding.e_goal
                                   in
                                let uu____1335 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_Tactics_Embedding.e_goal_nbe
                                   in
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "set_goals"
                                  FStar_Tactics_Monad.set_goals uu____1330
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Monad.set_goals uu____1335
                                  FStar_TypeChecker_NBETerm.e_unit
                                 in
                              let uu____1346 =
                                let uu____1349 =
                                  let uu____1350 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____1355 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_smt_goals"
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1350 FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1355
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____1366 =
                                  let uu____1369 =
                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "trivial"
                                      FStar_Tactics_Basic.trivial
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.trivial
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____1372 =
                                    let uu____1375 =
                                      let uu____1376 =
                                        e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any
                                         in
                                      let uu____1381 =
                                        FStar_Syntax_Embeddings.e_either
                                          FStar_Tactics_Embedding.e_exn
                                          FStar_Syntax_Embeddings.e_any
                                         in
                                      let uu____1388 =
                                        e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any
                                         in
                                      let uu____1393 =
                                        FStar_TypeChecker_NBETerm.e_either
                                          FStar_Tactics_Embedding.e_exn_nbe
                                          FStar_TypeChecker_NBETerm.e_any
                                         in
                                      FStar_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "catch"
                                        (fun uu____1415  ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_Syntax_Embeddings.e_any
                                        uu____1376 uu____1381
                                        (fun uu____1417  ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu____1388 uu____1393
                                       in
                                    let uu____1418 =
                                      let uu____1421 =
                                        let uu____1422 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____1427 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any
                                           in
                                        let uu____1434 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        let uu____1439 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any
                                           in
                                        FStar_Tactics_InterpFuns.mk_tac_step_2
                                          Prims.int_one "recover"
                                          (fun uu____1461  ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____1422 uu____1427
                                          (fun uu____1463  ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____1434 uu____1439
                                         in
                                      let uu____1464 =
                                        let uu____1467 =
                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intro"
                                            FStar_Tactics_Basic.intro
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Tactics_Basic.intro
                                            FStar_TypeChecker_NBETerm.e_unit
                                            FStar_Reflection_NBEEmbeddings.e_binder
                                           in
                                        let uu____1470 =
                                          let uu____1473 =
                                            let uu____1474 =
                                              FStar_Syntax_Embeddings.e_tuple2
                                                FStar_Reflection_Embeddings.e_binder
                                                FStar_Reflection_Embeddings.e_binder
                                               in
                                            let uu____1481 =
                                              FStar_TypeChecker_NBETerm.e_tuple2
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                               in
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "intro_rec"
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_Syntax_Embeddings.e_unit
                                              uu____1474
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_TypeChecker_NBETerm.e_unit
                                              uu____1481
                                             in
                                          let uu____1498 =
                                            let uu____1501 =
                                              let uu____1502 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_norm_step
                                                 in
                                              let uu____1507 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_norm_step
                                                 in
                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                Prims.int_zero "norm"
                                                FStar_Tactics_Basic.norm
                                                uu____1502
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.norm
                                                uu____1507
                                                FStar_TypeChecker_NBETerm.e_unit
                                               in
                                            let uu____1518 =
                                              let uu____1521 =
                                                let uu____1522 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____1527 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mk_tac_step_3
                                                  Prims.int_zero
                                                  "norm_term_env"
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_Embeddings.e_env
                                                  uu____1522
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                  uu____1527
                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                 in
                                              let uu____1538 =
                                                let uu____1541 =
                                                  let uu____1542 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step
                                                     in
                                                  let uu____1547 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step
                                                     in
                                                  FStar_Tactics_InterpFuns.mk_tac_step_2
                                                    Prims.int_zero
                                                    "norm_binder_type"
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1542
                                                    FStar_Reflection_Embeddings.e_binder
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1547
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                   in
                                                let uu____1558 =
                                                  let uu____1561 =
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
                                                  let uu____1566 =
                                                    let uu____1569 =
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
                                                    let uu____1572 =
                                                      let uu____1575 =
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
                                                      let uu____1578 =
                                                        let uu____1581 =
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
                                                        let uu____1584 =
                                                          let uu____1587 =
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
                                                          let uu____1590 =
                                                            let uu____1593 =
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
                                                            let uu____1596 =
                                                              let uu____1599
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
                                                              let uu____1602
                                                                =
                                                                let uu____1605
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
                                                                let uu____1612
                                                                  =
                                                                  let uu____1615
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
                                                                  let uu____1622
                                                                    =
                                                                    let uu____1625
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
                                                                    let uu____1628
                                                                    =
                                                                    let uu____1631
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
                                                                    let uu____1636
                                                                    =
                                                                    let uu____1639
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
                                                                    let uu____1642
                                                                    =
                                                                    let uu____1645
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
                                                                    let uu____1648
                                                                    =
                                                                    let uu____1651
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
                                                                    let uu____1654
                                                                    =
                                                                    let uu____1657
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1662
                                                                     ->
                                                                    fun
                                                                    uu____1663
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1667
                                                                    =
                                                                    let uu____1670
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
                                                                    let uu____1675
                                                                    =
                                                                    let uu____1678
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
                                                                    let uu____1683
                                                                    =
                                                                    let uu____1686
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
                                                                    let uu____1691
                                                                    =
                                                                    let uu____1694
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
                                                                    let uu____1699
                                                                    =
                                                                    let uu____1702
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
                                                                    let uu____1707
                                                                    =
                                                                    let uu____1710
                                                                    =
                                                                    let uu____1711
                                                                    =
                                                                    let uu____1724
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1724
                                                                     in
                                                                    let uu____1738
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1743
                                                                    =
                                                                    let uu____1756
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1756
                                                                     in
                                                                    let uu____1770
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1711
                                                                    uu____1738
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1743
                                                                    uu____1770
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1801
                                                                    =
                                                                    let uu____1804
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
                                                                    let uu____1807
                                                                    =
                                                                    let uu____1810
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
                                                                    let uu____1813
                                                                    =
                                                                    let uu____1816
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
                                                                    let uu____1819
                                                                    =
                                                                    let uu____1822
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
                                                                    let uu____1825
                                                                    =
                                                                    let uu____1828
                                                                    =
                                                                    let uu____1829
                                                                    =
                                                                    let uu____1838
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1838
                                                                     in
                                                                    let uu____1849
                                                                    =
                                                                    let uu____1858
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1858
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1829
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1849
                                                                     in
                                                                    let uu____1883
                                                                    =
                                                                    let uu____1886
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
                                                                    let uu____1889
                                                                    =
                                                                    let uu____1892
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
                                                                    let uu____1895
                                                                    =
                                                                    let uu____1898
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
                                                                    let uu____1901
                                                                    =
                                                                    let uu____1904
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
                                                                    let uu____1907
                                                                    =
                                                                    let uu____1910
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
                                                                    let uu____1913
                                                                    =
                                                                    let uu____1916
                                                                    =
                                                                    let uu____1917
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1922
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1917
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1922
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1933
                                                                    =
                                                                    let uu____1936
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
                                                                    let uu____1941
                                                                    =
                                                                    let uu____1944
                                                                    =
                                                                    let uu____1945
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1952
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1945
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1952
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1973
                                                                    =
                                                                    let uu____1976
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
                                                                    let uu____1981
                                                                    =
                                                                    let uu____1984
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
                                                                    let uu____1987
                                                                    =
                                                                    let uu____1990
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
                                                                    let uu____1993
                                                                    =
                                                                    let uu____1996
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
                                                                    let uu____1999
                                                                    =
                                                                    let uu____2002
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
                                                                    let uu____2007
                                                                    =
                                                                    let uu____2010
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____2017
                                                                     ->
                                                                    fun
                                                                    uu____2018
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____2021
                                                                    =
                                                                    let uu____2024
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
                                                                    uu____2032
                                                                     ->
                                                                    fun
                                                                    uu____2033
                                                                     ->
                                                                    fun
                                                                    uu____2034
                                                                     ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____2024]
                                                                     in
                                                                    uu____2010
                                                                    ::
                                                                    uu____2021
                                                                     in
                                                                    uu____2002
                                                                    ::
                                                                    uu____2007
                                                                     in
                                                                    uu____1996
                                                                    ::
                                                                    uu____1999
                                                                     in
                                                                    uu____1990
                                                                    ::
                                                                    uu____1993
                                                                     in
                                                                    uu____1984
                                                                    ::
                                                                    uu____1987
                                                                     in
                                                                    uu____1976
                                                                    ::
                                                                    uu____1981
                                                                     in
                                                                    uu____1944
                                                                    ::
                                                                    uu____1973
                                                                     in
                                                                    uu____1936
                                                                    ::
                                                                    uu____1941
                                                                     in
                                                                    uu____1916
                                                                    ::
                                                                    uu____1933
                                                                     in
                                                                    uu____1910
                                                                    ::
                                                                    uu____1913
                                                                     in
                                                                    uu____1904
                                                                    ::
                                                                    uu____1907
                                                                     in
                                                                    uu____1898
                                                                    ::
                                                                    uu____1901
                                                                     in
                                                                    uu____1892
                                                                    ::
                                                                    uu____1895
                                                                     in
                                                                    uu____1886
                                                                    ::
                                                                    uu____1889
                                                                     in
                                                                    uu____1828
                                                                    ::
                                                                    uu____1883
                                                                     in
                                                                    uu____1822
                                                                    ::
                                                                    uu____1825
                                                                     in
                                                                    uu____1816
                                                                    ::
                                                                    uu____1819
                                                                     in
                                                                    uu____1810
                                                                    ::
                                                                    uu____1813
                                                                     in
                                                                    uu____1804
                                                                    ::
                                                                    uu____1807
                                                                     in
                                                                    uu____1710
                                                                    ::
                                                                    uu____1801
                                                                     in
                                                                    uu____1702
                                                                    ::
                                                                    uu____1707
                                                                     in
                                                                    uu____1694
                                                                    ::
                                                                    uu____1699
                                                                     in
                                                                    uu____1686
                                                                    ::
                                                                    uu____1691
                                                                     in
                                                                    uu____1678
                                                                    ::
                                                                    uu____1683
                                                                     in
                                                                    uu____1670
                                                                    ::
                                                                    uu____1675
                                                                     in
                                                                    uu____1657
                                                                    ::
                                                                    uu____1667
                                                                     in
                                                                    uu____1651
                                                                    ::
                                                                    uu____1654
                                                                     in
                                                                    uu____1645
                                                                    ::
                                                                    uu____1648
                                                                     in
                                                                    uu____1639
                                                                    ::
                                                                    uu____1642
                                                                     in
                                                                    uu____1631
                                                                    ::
                                                                    uu____1636
                                                                     in
                                                                    uu____1625
                                                                    ::
                                                                    uu____1628
                                                                     in
                                                                  uu____1615
                                                                    ::
                                                                    uu____1622
                                                                   in
                                                                uu____1605 ::
                                                                  uu____1612
                                                                 in
                                                              uu____1599 ::
                                                                uu____1602
                                                               in
                                                            uu____1593 ::
                                                              uu____1596
                                                             in
                                                          uu____1587 ::
                                                            uu____1590
                                                           in
                                                        uu____1581 ::
                                                          uu____1584
                                                         in
                                                      uu____1575 ::
                                                        uu____1578
                                                       in
                                                    uu____1569 :: uu____1572
                                                     in
                                                  uu____1561 :: uu____1566
                                                   in
                                                uu____1541 :: uu____1558  in
                                              uu____1521 :: uu____1538  in
                                            uu____1501 :: uu____1518  in
                                          uu____1473 :: uu____1498  in
                                        uu____1467 :: uu____1470  in
                                      uu____1421 :: uu____1464  in
                                    uu____1375 :: uu____1418  in
                                  uu____1369 :: uu____1372  in
                                uu____1349 :: uu____1366  in
                              uu____1329 :: uu____1346  in
                            uu____1321 :: uu____1326  in
                          uu____1313 :: uu____1318  in
                        uu____1305 :: uu____1310  in
                      uu____1299 :: uu____1302  in
                    uu____1293 :: uu____1296  in
                  uu____1287 :: uu____1290  in
                uu____1267 :: uu____1284  in
              uu____1247 :: uu____1264  in
            uu____1241 :: uu____1244  in
          uu____1235 :: uu____1238  in
        uu____1229 :: uu____1232  in
      uu____1223 :: uu____1226  in
    FStar_All.pipe_left
      (fun uu____2045  -> FStar_Pervasives_Native.Some uu____2045) uu____1220
     in
  FStar_ST.op_Colon_Equals __primitive_steps_ref uu____1215 

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
                 let uu____2141 =
                   let uu____2146 =
                     let uu____2147 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____2147]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____2146  in
                 uu____2141 FStar_Pervasives_Native.None rng  in
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
      let em uu____2237 uu____2238 uu____2239 uu____2240 =
        failwith "Impossible: embedding tactic (1)?"  in
      let un t0 w n =
        let uu____2289 = unembed_tactic_1_alt ea er t0 n  in
        match uu____2289 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____2329 = f x  in FStar_Tactics_Monad.run uu____2329))
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      let uu____2345 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb em un uu____2345
  
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____2385 =
               let uu____2387 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____2389 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2387 uu____2389
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2385, rng)) is
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
                (let uu____2466 = FStar_ST.op_Bang tacdbg  in
                 if uu____2466
                 then
                   let uu____2490 = FStar_Syntax_Print.term_to_string tactic
                      in
                   FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                     uu____2490
                 else ());
                (let uu____2495 =
                   let uu____2502 = FStar_Syntax_Embeddings.type_of e_arg  in
                   let uu____2503 = FStar_Syntax_Embeddings.type_of e_res  in
                   FStar_TypeChecker_TcTerm.tc_tactic uu____2502 uu____2503
                     env tactic
                    in
                 match uu____2495 with
                 | (uu____2510,uu____2511,g) ->
                     ((let uu____2514 = FStar_ST.op_Bang tacdbg  in
                       if uu____2514
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
                       (let uu____2574 =
                          FStar_Util.record_time
                            (fun uu____2586  ->
                               let uu____2587 = tau arg  in
                               FStar_Tactics_Monad.run_safe uu____2587 ps)
                           in
                        match uu____2574 with
                        | (res,ms) ->
                            ((let uu____2605 = FStar_ST.op_Bang tacdbg  in
                              if uu____2605
                              then FStar_Util.print_string "}\n"
                              else ());
                             (let uu____2633 =
                                (FStar_ST.op_Bang tacdbg) ||
                                  (FStar_Options.tactics_info ())
                                 in
                              if uu____2633
                              then
                                let uu____2657 =
                                  FStar_Syntax_Print.term_to_string tactic
                                   in
                                let uu____2659 = FStar_Util.string_of_int ms
                                   in
                                let uu____2661 =
                                  FStar_Syntax_Print.lid_to_string
                                    env.FStar_TypeChecker_Env.curmodule
                                   in
                                FStar_Util.print3
                                  "Tactic %s ran in %s ms (%s)\n" uu____2657
                                  uu____2659 uu____2661
                              else ());
                             (match res with
                              | FStar_Tactics_Result.Success (ret,ps1) ->
                                  (FStar_List.iter
                                     (fun g1  ->
                                        let uu____2679 =
                                          FStar_Tactics_Types.is_irrelevant
                                            g1
                                           in
                                        if uu____2679
                                        then
                                          let uu____2682 =
                                            let uu____2684 =
                                              FStar_Tactics_Types.goal_env g1
                                               in
                                            let uu____2685 =
                                              FStar_Tactics_Types.goal_witness
                                                g1
                                               in
                                            FStar_TypeChecker_Rel.teq_nosmt_force
                                              uu____2684 uu____2685
                                              FStar_Syntax_Util.exp_unit
                                             in
                                          (if uu____2682
                                           then ()
                                           else
                                             (let uu____2689 =
                                                let uu____2691 =
                                                  let uu____2693 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_Syntax_Print.term_to_string
                                                    uu____2693
                                                   in
                                                FStar_Util.format1
                                                  "Irrelevant tactic witness does not unify with (): %s"
                                                  uu____2691
                                                 in
                                              failwith uu____2689))
                                        else ())
                                     (FStar_List.append
                                        ps1.FStar_Tactics_Types.goals
                                        ps1.FStar_Tactics_Types.smt_goals);
                                   (let uu____2698 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____2698
                                    then
                                      let uu____2722 =
                                        FStar_Common.string_of_list
                                          (fun imp  ->
                                             FStar_Syntax_Print.ctx_uvar_to_string
                                               imp.FStar_TypeChecker_Common.imp_uvar)
                                          ps1.FStar_Tactics_Types.all_implicits
                                         in
                                      FStar_Util.print1
                                        "About to check tactic implicits: %s\n"
                                        uu____2722
                                    else ());
                                   (let g1 =
                                      let uu___232_2730 =
                                        FStar_TypeChecker_Env.trivial_guard
                                         in
                                      {
                                        FStar_TypeChecker_Common.guard_f =
                                          (uu___232_2730.FStar_TypeChecker_Common.guard_f);
                                        FStar_TypeChecker_Common.deferred =
                                          (uu___232_2730.FStar_TypeChecker_Common.deferred);
                                        FStar_TypeChecker_Common.univ_ineqs =
                                          (uu___232_2730.FStar_TypeChecker_Common.univ_ineqs);
                                        FStar_TypeChecker_Common.implicits =
                                          (ps1.FStar_Tactics_Types.all_implicits)
                                      }  in
                                    let g2 =
                                      FStar_TypeChecker_Rel.solve_deferred_constraints
                                        env g1
                                       in
                                    (let uu____2733 = FStar_ST.op_Bang tacdbg
                                        in
                                     if uu____2733
                                     then
                                       let uu____2757 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length
                                              ps1.FStar_Tactics_Types.all_implicits)
                                          in
                                       let uu____2759 =
                                         FStar_Common.string_of_list
                                           (fun imp  ->
                                              FStar_Syntax_Print.ctx_uvar_to_string
                                                imp.FStar_TypeChecker_Common.imp_uvar)
                                           ps1.FStar_Tactics_Types.all_implicits
                                          in
                                       FStar_Util.print2
                                         "Checked %s implicits (1): %s\n"
                                         uu____2757 uu____2759
                                     else ());
                                    (let g3 =
                                       FStar_TypeChecker_Rel.resolve_implicits_tac
                                         env g2
                                        in
                                     (let uu____2768 =
                                        FStar_ST.op_Bang tacdbg  in
                                      if uu____2768
                                      then
                                        let uu____2792 =
                                          FStar_Util.string_of_int
                                            (FStar_List.length
                                               ps1.FStar_Tactics_Types.all_implicits)
                                           in
                                        let uu____2794 =
                                          FStar_Common.string_of_list
                                            (fun imp  ->
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 imp.FStar_TypeChecker_Common.imp_uvar)
                                            ps1.FStar_Tactics_Types.all_implicits
                                           in
                                        FStar_Util.print2
                                          "Checked %s implicits (2): %s\n"
                                          uu____2792 uu____2794
                                      else ());
                                     report_implicits rng_goal
                                       g3.FStar_TypeChecker_Common.implicits;
                                     (let uu____2803 =
                                        FStar_ST.op_Bang tacdbg  in
                                      if uu____2803
                                      then
                                        let uu____2827 =
                                          let uu____2828 =
                                            FStar_TypeChecker_Cfg.psc_subst
                                              ps1.FStar_Tactics_Types.psc
                                             in
                                          FStar_Tactics_Types.subst_proof_state
                                            uu____2828 ps1
                                           in
                                        FStar_Tactics_Printing.do_dump_proofstate
                                          uu____2827 "at the finish line"
                                      else ());
                                     ((FStar_List.append
                                         ps1.FStar_Tactics_Types.goals
                                         ps1.FStar_Tactics_Types.smt_goals),
                                       ret))))
                              | FStar_Tactics_Result.Failed (e,ps1) ->
                                  ((let uu____2837 =
                                      let uu____2838 =
                                        FStar_TypeChecker_Cfg.psc_subst
                                          ps1.FStar_Tactics_Types.psc
                                         in
                                      FStar_Tactics_Types.subst_proof_state
                                        uu____2838 ps1
                                       in
                                    FStar_Tactics_Printing.do_dump_proofstate
                                      uu____2837 "at the time of failure");
                                   (let texn_to_string e1 =
                                      match e1 with
                                      | FStar_Tactics_Types.TacticFailure s
                                          -> s
                                      | FStar_Tactics_Types.EExn t ->
                                          let uu____2851 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat "uncaught exception: "
                                            uu____2851
                                      | e2 -> FStar_Exn.raise e2  in
                                    let uu____2856 =
                                      let uu____2862 =
                                        let uu____2864 = texn_to_string e  in
                                        FStar_Util.format1
                                          "user tactic failed: %s" uu____2864
                                         in
                                      (FStar_Errors.Fatal_UserTacticFailure,
                                        uu____2862)
                                       in
                                    FStar_Errors.raise_error uu____2856
                                      ps1.FStar_Tactics_Types.entry_range))))))))
  