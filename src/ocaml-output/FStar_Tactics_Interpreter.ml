open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let unembed :
  'uuuuuu10 .
    'uuuuuu10 FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuuu10 FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a ->
      fun norm_cb ->
        let uu____34 = FStar_Syntax_Embeddings.unembed ea a in
        uu____34 true norm_cb
let embed :
  'uuuuuu51 .
    'uuuuuu51 FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuuu51 ->
          FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu____78 = FStar_Syntax_Embeddings.embed ea x in
          uu____78 r FStar_Pervasives_Native.None norm_cb
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____93 ->
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
    let uu____102 = FStar_Tactics_Native.list_all () in
    FStar_List.map step_from_native_step uu____102
let mk_total_step_1' :
  'uuuuuu129 'uuuuuu130 'uuuuuu131 'uuuuuu132 .
    Prims.int ->
      Prims.string ->
        ('uuuuuu129 -> 'uuuuuu130) ->
          'uuuuuu129 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu130 FStar_Syntax_Embeddings.embedding ->
              ('uuuuuu131 -> 'uuuuuu132) ->
                'uuuuuu131 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuuu132 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___19_199 =
                    FStar_Tactics_InterpFuns.mk_total_step_1 uarity nm f ea
                      er nf ena enr in
                  let uu____200 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu____200;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___19_199.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___19_199.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___19_199.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___19_199.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___19_199.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___19_199.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___19_199.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_1'_psc :
  'uuuuuu225 'uuuuuu226 'uuuuuu227 'uuuuuu228 .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'uuuuuu225 -> 'uuuuuu226) ->
          'uuuuuu225 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu226 FStar_Syntax_Embeddings.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'uuuuuu227 -> 'uuuuuu228) ->
                'uuuuuu227 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuuu228 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___29_305 =
                    FStar_Tactics_InterpFuns.mk_total_step_1_psc uarity nm f
                      ea er nf ena enr in
                  let uu____306 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu____306;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___29_305.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___29_305.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___29_305.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___29_305.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___29_305.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___29_305.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___29_305.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_2' :
  'uuuuuu339 'uuuuuu340 'uuuuuu341 'uuuuuu342 'uuuuuu343 'uuuuuu344 .
    Prims.int ->
      Prims.string ->
        ('uuuuuu339 -> 'uuuuuu340 -> 'uuuuuu341) ->
          'uuuuuu339 FStar_Syntax_Embeddings.embedding ->
            'uuuuuu340 FStar_Syntax_Embeddings.embedding ->
              'uuuuuu341 FStar_Syntax_Embeddings.embedding ->
                ('uuuuuu342 -> 'uuuuuu343 -> 'uuuuuu344) ->
                  'uuuuuu342 FStar_TypeChecker_NBETerm.embedding ->
                    'uuuuuu343 FStar_TypeChecker_NBETerm.embedding ->
                      'uuuuuu344 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___41_439 =
                        FStar_Tactics_InterpFuns.mk_total_step_2 uarity nm f
                          ea eb er nf ena enb enr in
                      let uu____440 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm) in
                      {
                        FStar_TypeChecker_Cfg.name = uu____440;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___41_439.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___41_439.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___41_439.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___41_439.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___41_439.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___41_439.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___41_439.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
let (__primitive_steps_ref :
  FStar_TypeChecker_Cfg.primitive_step Prims.list
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____459 ->
    let uu____462 =
      let uu____465 = FStar_ST.op_Bang __primitive_steps_ref in
      FStar_Util.must uu____465 in
    let uu____486 = native_tactics_steps () in
    FStar_List.append uu____462 uu____486
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
               let uu____538 =
                 let uu____539 =
                   let uu____548 =
                     embed FStar_Tactics_Embedding.e_proofstate rng
                       proof_state ncb in
                   FStar_Syntax_Syntax.as_arg uu____548 in
                 [uu____539] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____538 rng in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe] in
             let norm_f =
               let uu____589 = FStar_Options.tactics_nbe () in
               if uu____589
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps in
             let result =
               let uu____608 = primitive_steps () in
               norm_f uu____608 steps
                 proof_state.FStar_Tactics_Types.main_context tm in
             let res =
               let uu____616 = FStar_Tactics_Embedding.e_result eb in
               unembed uu____616 result ncb in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu____629 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____629
                   (fun uu____633 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu____638 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____638
                   (fun uu____642 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu____645 =
                   let uu____650 =
                     let uu____651 = FStar_Syntax_Print.term_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____651 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____650) in
                 FStar_Errors.raise_error uu____645
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
               let uu____692 =
                 let uu____693 =
                   let uu____698 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state in
                   FStar_TypeChecker_NBETerm.as_arg uu____698 in
                 [uu____693] in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____692 in
             let res =
               let uu____712 = FStar_Tactics_Embedding.e_result_nbe eb in
               FStar_TypeChecker_NBETerm.unembed uu____712 cb result in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu____725 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____725
                   (fun uu____729 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu____734 = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu____734
                   (fun uu____738 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu____741 =
                   let uu____746 =
                     let uu____747 =
                       FStar_TypeChecker_NBETerm.t_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____747 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____746) in
                 FStar_Errors.raise_error uu____741
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
              let uu____803 =
                let uu____804 = FStar_Syntax_Syntax.as_arg x_tm in
                [uu____804] in
              FStar_Syntax_Syntax.mk_Tm_app f uu____803 rng in
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
              let uu____879 =
                let uu____880 = FStar_TypeChecker_NBETerm.as_arg x_tm in
                [uu____880] in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____879 in
            unembed_tactic_nbe_0 er cb app
let e_tactic_thunk :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er ->
    let uu____911 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____918 ->
         fun uu____919 ->
           fun uu____920 ->
             fun uu____921 ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t ->
         fun w ->
           fun cb ->
             let uu____933 =
               let uu____936 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb in
               uu____936 () in
             FStar_Pervasives_Native.Some uu____933) uu____911
let e_tactic_nbe_thunk :
  'r .
    'r FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er ->
    let uu____963 =
      FStar_TypeChecker_NBETerm.mk_t
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
    let uu____964 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb ->
         fun uu____970 ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb ->
         fun t ->
           let uu____978 =
             let uu____981 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t in
             uu____981 () in
           FStar_Pervasives_Native.Some uu____978) uu____963 uu____964
let e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    fun er ->
      let uu____1025 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____1035 ->
           fun uu____1036 ->
             fun uu____1037 ->
               fun uu____1038 -> failwith "Impossible: embedding tactic (1)?")
        (fun t ->
           fun w ->
             fun cb ->
               let uu____1052 = unembed_tactic_1 ea er t cb in
               FStar_Pervasives_Native.Some uu____1052) uu____1025
let e_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    fun er ->
      let uu____1099 =
        FStar_TypeChecker_NBETerm.mk_t
          (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
      let uu____1100 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb ->
           fun uu____1109 -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb ->
           fun t ->
             let uu____1119 = unembed_tactic_nbe_1 ea er cb t in
             FStar_Pervasives_Native.Some uu____1119) uu____1099 uu____1100
let (uu___143 : unit) =
  let uu____1131 =
    let uu____1136 =
      let uu____1139 =
        mk_total_step_1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit in
      let uu____1140 =
        let uu____1143 =
          mk_total_step_2' Prims.int_zero "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe in
        let uu____1144 =
          let uu____1147 =
            mk_total_step_1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe in
          let uu____1148 =
            let uu____1151 =
              mk_total_step_1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe in
            let uu____1152 =
              let uu____1155 =
                let uu____1156 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal in
                let uu____1161 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe in
                mk_total_step_1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____1156
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____1161 in
              let uu____1170 =
                let uu____1173 =
                  let uu____1174 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal in
                  let uu____1179 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe in
                  mk_total_step_1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____1174
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____1179 in
                let uu____1188 =
                  let uu____1191 =
                    mk_total_step_1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env in
                  let uu____1192 =
                    let uu____1195 =
                      mk_total_step_1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term in
                    let uu____1196 =
                      let uu____1199 =
                        mk_total_step_1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term in
                      let uu____1200 =
                        let uu____1203 =
                          mk_total_step_1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool in
                        let uu____1204 =
                          let uu____1207 =
                            mk_total_step_1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string in
                          let uu____1208 =
                            let uu____1211 =
                              mk_total_step_2' Prims.int_zero "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe in
                            let uu____1212 =
                              let uu____1215 =
                                let uu____1216 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Tactics_Embedding.e_goal in
                                let uu____1221 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_Tactics_Embedding.e_goal_nbe in
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "set_goals"
                                  FStar_Tactics_Monad.set_goals uu____1216
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Monad.set_goals uu____1221
                                  FStar_TypeChecker_NBETerm.e_unit in
                              let uu____1230 =
                                let uu____1233 =
                                  let uu____1234 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal in
                                  let uu____1239 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe in
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_smt_goals"
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1234 FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_smt_goals
                                    uu____1239
                                    FStar_TypeChecker_NBETerm.e_unit in
                                let uu____1248 =
                                  let uu____1251 =
                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                      Prims.int_zero "trivial"
                                      FStar_Tactics_Basic.trivial
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.trivial
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit in
                                  let uu____1252 =
                                    let uu____1255 =
                                      let uu____1256 =
                                        e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu____1261 =
                                        FStar_Syntax_Embeddings.e_either
                                          FStar_Tactics_Embedding.e_exn
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu____1268 =
                                        e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any in
                                      let uu____1273 =
                                        FStar_TypeChecker_NBETerm.e_either
                                          FStar_Tactics_Embedding.e_exn_nbe
                                          FStar_TypeChecker_NBETerm.e_any in
                                      FStar_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "catch"
                                        (fun uu____1293 ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_Syntax_Embeddings.e_any
                                        uu____1256 uu____1261
                                        (fun uu____1295 ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu____1268 uu____1273 in
                                    let uu____1296 =
                                      let uu____1299 =
                                        let uu____1300 =
                                          e_tactic_thunk
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu____1305 =
                                          FStar_Syntax_Embeddings.e_either
                                            FStar_Tactics_Embedding.e_exn
                                            FStar_Syntax_Embeddings.e_any in
                                        let uu____1312 =
                                          e_tactic_nbe_thunk
                                            FStar_TypeChecker_NBETerm.e_any in
                                        let uu____1317 =
                                          FStar_TypeChecker_NBETerm.e_either
                                            FStar_Tactics_Embedding.e_exn_nbe
                                            FStar_TypeChecker_NBETerm.e_any in
                                        FStar_Tactics_InterpFuns.mk_tac_step_2
                                          Prims.int_one "recover"
                                          (fun uu____1337 ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_Syntax_Embeddings.e_any
                                          uu____1300 uu____1305
                                          (fun uu____1339 ->
                                             FStar_Tactics_Basic.recover)
                                          FStar_TypeChecker_NBETerm.e_any
                                          uu____1312 uu____1317 in
                                      let uu____1340 =
                                        let uu____1343 =
                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intro"
                                            FStar_Tactics_Basic.intro
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Tactics_Basic.intro
                                            FStar_TypeChecker_NBETerm.e_unit
                                            FStar_Reflection_NBEEmbeddings.e_binder in
                                        let uu____1344 =
                                          let uu____1347 =
                                            let uu____1348 =
                                              FStar_Syntax_Embeddings.e_tuple2
                                                FStar_Reflection_Embeddings.e_binder
                                                FStar_Reflection_Embeddings.e_binder in
                                            let uu____1355 =
                                              FStar_TypeChecker_NBETerm.e_tuple2
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                FStar_Reflection_NBEEmbeddings.e_binder in
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "intro_rec"
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_Syntax_Embeddings.e_unit
                                              uu____1348
                                              FStar_Tactics_Basic.intro_rec
                                              FStar_TypeChecker_NBETerm.e_unit
                                              uu____1355 in
                                          let uu____1370 =
                                            let uu____1373 =
                                              let uu____1374 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_norm_step in
                                              let uu____1379 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_norm_step in
                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                Prims.int_zero "norm"
                                                FStar_Tactics_Basic.norm
                                                uu____1374
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.norm
                                                uu____1379
                                                FStar_TypeChecker_NBETerm.e_unit in
                                            let uu____1388 =
                                              let uu____1391 =
                                                let uu____1392 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step in
                                                let uu____1397 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step in
                                                FStar_Tactics_InterpFuns.mk_tac_step_3
                                                  Prims.int_zero
                                                  "norm_term_env"
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_Embeddings.e_env
                                                  uu____1392
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Tactics_Basic.norm_term_env
                                                  FStar_Reflection_NBEEmbeddings.e_env
                                                  uu____1397
                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                  FStar_Reflection_NBEEmbeddings.e_term in
                                              let uu____1406 =
                                                let uu____1409 =
                                                  let uu____1410 =
                                                    FStar_Syntax_Embeddings.e_list
                                                      FStar_Syntax_Embeddings.e_norm_step in
                                                  let uu____1415 =
                                                    FStar_TypeChecker_NBETerm.e_list
                                                      FStar_TypeChecker_NBETerm.e_norm_step in
                                                  FStar_Tactics_InterpFuns.mk_tac_step_2
                                                    Prims.int_zero
                                                    "norm_binder_type"
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1410
                                                    FStar_Reflection_Embeddings.e_binder
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.norm_binder_type
                                                    uu____1415
                                                    FStar_Reflection_NBEEmbeddings.e_binder
                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                let uu____1424 =
                                                  let uu____1427 =
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
                                                  let uu____1428 =
                                                    let uu____1431 =
                                                      FStar_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "binder_retype"
                                                        FStar_Tactics_Basic.binder_retype
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.binder_retype
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_unit in
                                                    let uu____1432 =
                                                      let uu____1435 =
                                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "revert"
                                                          FStar_Tactics_Basic.revert
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.revert
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit in
                                                      let uu____1436 =
                                                        let uu____1439 =
                                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "clear_top"
                                                            FStar_Tactics_Basic.clear_top
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.clear_top
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit in
                                                        let uu____1440 =
                                                          let uu____1443 =
                                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "clear"
                                                              FStar_Tactics_Basic.clear
                                                              FStar_Reflection_Embeddings.e_binder
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.clear
                                                              FStar_Reflection_NBEEmbeddings.e_binder
                                                              FStar_TypeChecker_NBETerm.e_unit in
                                                          let uu____1444 =
                                                            let uu____1447 =
                                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "rewrite"
                                                                FStar_Tactics_Basic.rewrite
                                                                FStar_Reflection_Embeddings.e_binder
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.rewrite
                                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                                FStar_TypeChecker_NBETerm.e_unit in
                                                            let uu____1448 =
                                                              let uu____1451
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
                                                              let uu____1452
                                                                =
                                                                let uu____1455
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
                                                                let uu____1456
                                                                  =
                                                                  let uu____1459
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
                                                                  let uu____1460
                                                                    =
                                                                    let uu____1463
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "t_apply_lemma"
                                                                    FStar_Tactics_Basic.t_apply_lemma
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_apply_lemma
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1464
                                                                    =
                                                                    let uu____1467
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
                                                                    let uu____1468
                                                                    =
                                                                    let uu____1471
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
                                                                    let uu____1472
                                                                    =
                                                                    let uu____1475
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
                                                                    let uu____1476
                                                                    =
                                                                    let uu____1479
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
                                                                    let uu____1480
                                                                    =
                                                                    let uu____1483
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1486
                                                                    ->
                                                                    fun
                                                                    uu____1487
                                                                    ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____1490
                                                                    =
                                                                    let uu____1493
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
                                                                    let uu____1494
                                                                    =
                                                                    let uu____1497
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
                                                                    let uu____1498
                                                                    =
                                                                    let uu____1501
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
                                                                    let uu____1502
                                                                    =
                                                                    let uu____1505
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
                                                                    let uu____1506
                                                                    =
                                                                    let uu____1509
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
                                                                    let uu____1510
                                                                    =
                                                                    let uu____1513
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_all"
                                                                    FStar_Tactics_Basic.dump_all
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dump_all
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1514
                                                                    =
                                                                    let uu____1517
                                                                    =
                                                                    let uu____1518
                                                                    =
                                                                    let uu____1530
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1530 in
                                                                    let uu____1541
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu____1546
                                                                    =
                                                                    let uu____1558
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1558 in
                                                                    let uu____1569
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1518
                                                                    uu____1541
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1546
                                                                    uu____1569
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu____1596
                                                                    =
                                                                    let uu____1599
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
                                                                    let uu____1600
                                                                    =
                                                                    let uu____1603
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
                                                                    let uu____1604
                                                                    =
                                                                    let uu____1607
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
                                                                    let uu____1608
                                                                    =
                                                                    let uu____1611
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
                                                                    let uu____1612
                                                                    =
                                                                    let uu____1615
                                                                    =
                                                                    let uu____1616
                                                                    =
                                                                    let uu____1625
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1625 in
                                                                    let uu____1636
                                                                    =
                                                                    let uu____1645
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1645 in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1616
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1636 in
                                                                    let uu____1668
                                                                    =
                                                                    let uu____1671
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
                                                                    let uu____1672
                                                                    =
                                                                    let uu____1675
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
                                                                    let uu____1676
                                                                    =
                                                                    let uu____1679
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
                                                                    let uu____1680
                                                                    =
                                                                    let uu____1683
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
                                                                    let uu____1684
                                                                    =
                                                                    let uu____1687
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
                                                                    let uu____1688
                                                                    =
                                                                    let uu____1691
                                                                    =
                                                                    let uu____1692
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu____1697
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1692
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1697
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu____1706
                                                                    =
                                                                    let uu____1709
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
                                                                    let uu____1710
                                                                    =
                                                                    let uu____1713
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "match_env"
                                                                    FStar_Tactics_Basic.match_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.match_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu____1714
                                                                    =
                                                                    let uu____1717
                                                                    =
                                                                    let uu____1718
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu____1723
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1718
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1723
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu____1732
                                                                    =
                                                                    let uu____1735
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
                                                                    let uu____1736
                                                                    =
                                                                    let uu____1739
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
                                                                    let uu____1740
                                                                    =
                                                                    let uu____1743
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
                                                                    let uu____1744
                                                                    =
                                                                    let uu____1747
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
                                                                    let uu____1748
                                                                    =
                                                                    let uu____1751
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
                                                                    let uu____1752
                                                                    =
                                                                    let uu____1755
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1758
                                                                    ->
                                                                    fun
                                                                    uu____1759
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu____1760
                                                                    =
                                                                    let uu____1763
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
                                                                    uu____1767
                                                                    ->
                                                                    fun
                                                                    uu____1768
                                                                    ->
                                                                    fun
                                                                    uu____1769
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    [uu____1763] in
                                                                    uu____1755
                                                                    ::
                                                                    uu____1760 in
                                                                    uu____1751
                                                                    ::
                                                                    uu____1752 in
                                                                    uu____1747
                                                                    ::
                                                                    uu____1748 in
                                                                    uu____1743
                                                                    ::
                                                                    uu____1744 in
                                                                    uu____1739
                                                                    ::
                                                                    uu____1740 in
                                                                    uu____1735
                                                                    ::
                                                                    uu____1736 in
                                                                    uu____1717
                                                                    ::
                                                                    uu____1732 in
                                                                    uu____1713
                                                                    ::
                                                                    uu____1714 in
                                                                    uu____1709
                                                                    ::
                                                                    uu____1710 in
                                                                    uu____1691
                                                                    ::
                                                                    uu____1706 in
                                                                    uu____1687
                                                                    ::
                                                                    uu____1688 in
                                                                    uu____1683
                                                                    ::
                                                                    uu____1684 in
                                                                    uu____1679
                                                                    ::
                                                                    uu____1680 in
                                                                    uu____1675
                                                                    ::
                                                                    uu____1676 in
                                                                    uu____1671
                                                                    ::
                                                                    uu____1672 in
                                                                    uu____1615
                                                                    ::
                                                                    uu____1668 in
                                                                    uu____1611
                                                                    ::
                                                                    uu____1612 in
                                                                    uu____1607
                                                                    ::
                                                                    uu____1608 in
                                                                    uu____1603
                                                                    ::
                                                                    uu____1604 in
                                                                    uu____1599
                                                                    ::
                                                                    uu____1600 in
                                                                    uu____1517
                                                                    ::
                                                                    uu____1596 in
                                                                    uu____1513
                                                                    ::
                                                                    uu____1514 in
                                                                    uu____1509
                                                                    ::
                                                                    uu____1510 in
                                                                    uu____1505
                                                                    ::
                                                                    uu____1506 in
                                                                    uu____1501
                                                                    ::
                                                                    uu____1502 in
                                                                    uu____1497
                                                                    ::
                                                                    uu____1498 in
                                                                    uu____1493
                                                                    ::
                                                                    uu____1494 in
                                                                    uu____1483
                                                                    ::
                                                                    uu____1490 in
                                                                    uu____1479
                                                                    ::
                                                                    uu____1480 in
                                                                    uu____1475
                                                                    ::
                                                                    uu____1476 in
                                                                    uu____1471
                                                                    ::
                                                                    uu____1472 in
                                                                    uu____1467
                                                                    ::
                                                                    uu____1468 in
                                                                    uu____1463
                                                                    ::
                                                                    uu____1464 in
                                                                  uu____1459
                                                                    ::
                                                                    uu____1460 in
                                                                uu____1455 ::
                                                                  uu____1456 in
                                                              uu____1451 ::
                                                                uu____1452 in
                                                            uu____1447 ::
                                                              uu____1448 in
                                                          uu____1443 ::
                                                            uu____1444 in
                                                        uu____1439 ::
                                                          uu____1440 in
                                                      uu____1435 ::
                                                        uu____1436 in
                                                    uu____1431 :: uu____1432 in
                                                  uu____1427 :: uu____1428 in
                                                uu____1409 :: uu____1424 in
                                              uu____1391 :: uu____1406 in
                                            uu____1373 :: uu____1388 in
                                          uu____1347 :: uu____1370 in
                                        uu____1343 :: uu____1344 in
                                      uu____1299 :: uu____1340 in
                                    uu____1255 :: uu____1296 in
                                  uu____1251 :: uu____1252 in
                                uu____1233 :: uu____1248 in
                              uu____1215 :: uu____1230 in
                            uu____1211 :: uu____1212 in
                          uu____1207 :: uu____1208 in
                        uu____1203 :: uu____1204 in
                      uu____1199 :: uu____1200 in
                    uu____1195 :: uu____1196 in
                  uu____1191 :: uu____1192 in
                uu____1173 :: uu____1188 in
              uu____1155 :: uu____1170 in
            uu____1151 :: uu____1152 in
          uu____1147 :: uu____1148 in
        uu____1143 :: uu____1144 in
      uu____1139 :: uu____1140 in
    FStar_All.pipe_left
      (fun uu____1778 -> FStar_Pervasives_Native.Some uu____1778) uu____1136 in
  FStar_ST.op_Colon_Equals __primitive_steps_ref uu____1131

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
                 let uu____1857 =
                   let uu____1858 = FStar_Syntax_Syntax.as_arg x_tm in
                   [uu____1858] in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____1857 rng in
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
      let em uu____1947 uu____1948 uu____1949 uu____1950 =
        failwith "Impossible: embedding tactic (1)?" in
      let un t0 w n =
        let uu____1996 = unembed_tactic_1_alt ea er t0 n in
        match uu____1996 with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x ->
                  let uu____2036 = f x in FStar_Tactics_Monad.run uu____2036))
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu____2052 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb em un uu____2052
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng ->
    fun is ->
      let errs =
        FStar_List.map
          (fun imp ->
             let uu____2089 =
               let uu____2090 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____2091 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____2090 uu____2091
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____2089, rng)) is in
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
                (let uu____2164 = FStar_ST.op_Bang tacdbg in
                 if uu____2164
                 then
                   let uu____2171 = FStar_Syntax_Print.term_to_string tactic in
                   FStar_Util.print1 "Typechecking tactic: (%s) {\n"
                     uu____2171
                 else ());
                (let uu____2173 =
                   let uu____2180 = FStar_Syntax_Embeddings.type_of e_arg in
                   let uu____2181 = FStar_Syntax_Embeddings.type_of e_res in
                   FStar_TypeChecker_TcTerm.tc_tactic uu____2180 uu____2181
                     env tactic in
                 match uu____2173 with
                 | (uu____2188, uu____2189, g) ->
                     ((let uu____2192 = FStar_ST.op_Bang tacdbg in
                       if uu____2192
                       then FStar_Util.print_string "}\n"
                       else ());
                      FStar_TypeChecker_Rel.force_trivial_guard env g;
                      FStar_Errors.stop_if_err ();
                      (let tau =
                         unembed_tactic_1 e_arg e_res tactic
                           FStar_Syntax_Embeddings.id_norm_cb in
                       let uu____2209 =
                         FStar_Util.record_time
                           (fun uu____2220 ->
                              let uu____2221 = tau arg in
                              FStar_Tactics_Monad.run_safe uu____2221 ps) in
                       match uu____2209 with
                       | (res, ms) ->
                           ((let uu____2237 = FStar_ST.op_Bang tacdbg in
                             if uu____2237
                             then FStar_Util.print_string "}\n"
                             else ());
                            (let uu____2246 =
                               (FStar_ST.op_Bang tacdbg) ||
                                 (FStar_Options.tactics_info ()) in
                             if uu____2246
                             then
                               let uu____2253 =
                                 FStar_Syntax_Print.term_to_string tactic in
                               let uu____2254 = FStar_Util.string_of_int ms in
                               let uu____2255 =
                                 FStar_Syntax_Print.lid_to_string
                                   env.FStar_TypeChecker_Env.curmodule in
                               FStar_Util.print3
                                 "Tactic %s ran in %s ms (%s)\n" uu____2253
                                 uu____2254 uu____2255
                             else ());
                            (match res with
                             | FStar_Tactics_Result.Success (ret, ps1) ->
                                 (FStar_List.iter
                                    (fun g1 ->
                                       let uu____2270 =
                                         FStar_Tactics_Types.is_irrelevant g1 in
                                       if uu____2270
                                       then
                                         let uu____2271 =
                                           let uu____2272 =
                                             FStar_Tactics_Types.goal_env g1 in
                                           let uu____2273 =
                                             FStar_Tactics_Types.goal_witness
                                               g1 in
                                           FStar_TypeChecker_Rel.teq_nosmt_force
                                             uu____2272 uu____2273
                                             FStar_Syntax_Util.exp_unit in
                                         (if uu____2271
                                          then ()
                                          else
                                            (let uu____2275 =
                                               let uu____2276 =
                                                 let uu____2277 =
                                                   FStar_Tactics_Types.goal_witness
                                                     g1 in
                                                 FStar_Syntax_Print.term_to_string
                                                   uu____2277 in
                                               FStar_Util.format1
                                                 "Irrelevant tactic witness does not unify with (): %s"
                                                 uu____2276 in
                                             failwith uu____2275))
                                       else ())
                                    (FStar_List.append
                                       ps1.FStar_Tactics_Types.goals
                                       ps1.FStar_Tactics_Types.smt_goals);
                                  (let uu____2280 = FStar_ST.op_Bang tacdbg in
                                   if uu____2280
                                   then
                                     let uu____2287 =
                                       FStar_Common.string_of_list
                                         (fun imp ->
                                            FStar_Syntax_Print.ctx_uvar_to_string
                                              imp.FStar_TypeChecker_Common.imp_uvar)
                                         ps1.FStar_Tactics_Types.all_implicits in
                                     FStar_Util.print1
                                       "About to check tactic implicits: %s\n"
                                       uu____2287
                                   else ());
                                  (let g1 =
                                     let uu___231_2292 =
                                       FStar_TypeChecker_Env.trivial_guard in
                                     {
                                       FStar_TypeChecker_Common.guard_f =
                                         (uu___231_2292.FStar_TypeChecker_Common.guard_f);
                                       FStar_TypeChecker_Common.deferred_to_tac
                                         =
                                         (uu___231_2292.FStar_TypeChecker_Common.deferred_to_tac);
                                       FStar_TypeChecker_Common.deferred =
                                         (uu___231_2292.FStar_TypeChecker_Common.deferred);
                                       FStar_TypeChecker_Common.univ_ineqs =
                                         (uu___231_2292.FStar_TypeChecker_Common.univ_ineqs);
                                       FStar_TypeChecker_Common.implicits =
                                         (ps1.FStar_Tactics_Types.all_implicits)
                                     } in
                                   let g2 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env g1 in
                                   (let uu____2295 = FStar_ST.op_Bang tacdbg in
                                    if uu____2295
                                    then
                                      let uu____2302 =
                                        FStar_Util.string_of_int
                                          (FStar_List.length
                                             ps1.FStar_Tactics_Types.all_implicits) in
                                      let uu____2303 =
                                        FStar_Common.string_of_list
                                          (fun imp ->
                                             FStar_Syntax_Print.ctx_uvar_to_string
                                               imp.FStar_TypeChecker_Common.imp_uvar)
                                          ps1.FStar_Tactics_Types.all_implicits in
                                      FStar_Util.print2
                                        "Checked %s implicits (1): %s\n"
                                        uu____2302 uu____2303
                                    else ());
                                   (let g3 =
                                      FStar_TypeChecker_Rel.resolve_implicits_tac
                                        env g2 in
                                    (let uu____2309 = FStar_ST.op_Bang tacdbg in
                                     if uu____2309
                                     then
                                       let uu____2316 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length
                                              ps1.FStar_Tactics_Types.all_implicits) in
                                       let uu____2317 =
                                         FStar_Common.string_of_list
                                           (fun imp ->
                                              FStar_Syntax_Print.ctx_uvar_to_string
                                                imp.FStar_TypeChecker_Common.imp_uvar)
                                           ps1.FStar_Tactics_Types.all_implicits in
                                       FStar_Util.print2
                                         "Checked %s implicits (2): %s\n"
                                         uu____2316 uu____2317
                                     else ());
                                    report_implicits rng_goal
                                      g3.FStar_TypeChecker_Common.implicits;
                                    (let uu____2323 = FStar_ST.op_Bang tacdbg in
                                     if uu____2323
                                     then
                                       let uu____2330 =
                                         let uu____2331 =
                                           FStar_TypeChecker_Cfg.psc_subst
                                             ps1.FStar_Tactics_Types.psc in
                                         FStar_Tactics_Types.subst_proof_state
                                           uu____2331 ps1 in
                                       FStar_Tactics_Printing.do_dump_proofstate
                                         uu____2330 "at the finish line"
                                     else ());
                                    ((FStar_List.append
                                        ps1.FStar_Tactics_Types.goals
                                        ps1.FStar_Tactics_Types.smt_goals),
                                      ret))))
                             | FStar_Tactics_Result.Failed (e, ps1) ->
                                 ((let uu____2338 =
                                     let uu____2339 =
                                       FStar_TypeChecker_Cfg.psc_subst
                                         ps1.FStar_Tactics_Types.psc in
                                     FStar_Tactics_Types.subst_proof_state
                                       uu____2339 ps1 in
                                   FStar_Tactics_Printing.do_dump_proofstate
                                     uu____2338 "at the time of failure");
                                  (let texn_to_string e1 =
                                     match e1 with
                                     | FStar_Tactics_Common.TacticFailure s
                                         -> s
                                     | FStar_Tactics_Common.EExn t ->
                                         let uu____2348 =
                                           FStar_Syntax_Print.term_to_string
                                             t in
                                         Prims.op_Hat "uncaught exception: "
                                           uu____2348
                                     | e2 -> FStar_Exn.raise e2 in
                                   let uu____2350 =
                                     let uu____2355 =
                                       let uu____2356 = texn_to_string e in
                                       FStar_Util.format1
                                         "user tactic failed: %s" uu____2356 in
                                     (FStar_Errors.Fatal_UserTacticFailure,
                                       uu____2355) in
                                   FStar_Errors.raise_error uu____2350
                                     ps1.FStar_Tactics_Types.entry_range)))))))