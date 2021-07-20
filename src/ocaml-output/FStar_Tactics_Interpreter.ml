open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let unembed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb ->
          'uuuuu FStar_Pervasives_Native.option
  =
  fun ea ->
    fun a ->
      fun norm_cb ->
        let uu___ = FStar_Syntax_Embeddings.unembed ea a in
        uu___ true norm_cb
let embed :
  'uuuuu .
    'uuuuu FStar_Syntax_Embeddings.embedding ->
      FStar_Range.range ->
        'uuuuu -> FStar_Syntax_Embeddings.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun ea ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu___ = FStar_Syntax_Embeddings.embed ea x in
          uu___ r FStar_Pervasives_Native.None norm_cb
let (native_tactics_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu___ ->
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
    let uu___1 = FStar_Tactics_Native.list_all () in
    FStar_List.map step_from_native_step uu___1
let mk_total_step_1' :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    Prims.int ->
      Prims.string ->
        ('uuuuu -> 'uuuuu1) ->
          'uuuuu FStar_Syntax_Embeddings.embedding ->
            'uuuuu1 FStar_Syntax_Embeddings.embedding ->
              ('uuuuu2 -> 'uuuuu3) ->
                'uuuuu2 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuu3 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___ =
                    FStar_Tactics_InterpFuns.mk_total_step_1 uarity nm f ea
                      er nf ena enr in
                  let uu___1 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu___1;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_1'_psc :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    Prims.int ->
      Prims.string ->
        (FStar_TypeChecker_Cfg.psc -> 'uuuuu -> 'uuuuu1) ->
          'uuuuu FStar_Syntax_Embeddings.embedding ->
            'uuuuu1 FStar_Syntax_Embeddings.embedding ->
              (FStar_TypeChecker_Cfg.psc -> 'uuuuu2 -> 'uuuuu3) ->
                'uuuuu2 FStar_TypeChecker_NBETerm.embedding ->
                  'uuuuu3 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___ =
                    FStar_Tactics_InterpFuns.mk_total_step_1_psc uarity nm f
                      ea er nf ena enr in
                  let uu___1 =
                    FStar_Ident.lid_of_str
                      (Prims.op_Hat "FStar.Tactics.Types." nm) in
                  {
                    FStar_TypeChecker_Cfg.name = uu___1;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
let mk_total_step_2' :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    Prims.int ->
      Prims.string ->
        ('uuuuu -> 'uuuuu1 -> 'uuuuu2) ->
          'uuuuu FStar_Syntax_Embeddings.embedding ->
            'uuuuu1 FStar_Syntax_Embeddings.embedding ->
              'uuuuu2 FStar_Syntax_Embeddings.embedding ->
                ('uuuuu3 -> 'uuuuu4 -> 'uuuuu5) ->
                  'uuuuu3 FStar_TypeChecker_NBETerm.embedding ->
                    'uuuuu4 FStar_TypeChecker_NBETerm.embedding ->
                      'uuuuu5 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___ =
                        FStar_Tactics_InterpFuns.mk_total_step_2 uarity nm f
                          ea eb er nf ena enb enr in
                      let uu___1 =
                        FStar_Ident.lid_of_str
                          (Prims.op_Hat "FStar.Tactics.Types." nm) in
                      {
                        FStar_TypeChecker_Cfg.name = uu___1;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
let (__primitive_steps_ref :
  FStar_TypeChecker_Cfg.primitive_step Prims.list
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_ST.op_Bang __primitive_steps_ref in
      FStar_Util.must uu___2 in
    let uu___2 = native_tactics_steps () in FStar_List.append uu___1 uu___2
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
               let uu___ =
                 let uu___1 =
                   let uu___2 =
                     embed FStar_Tactics_Embedding.e_proofstate rng
                       proof_state ncb in
                   FStar_Syntax_Syntax.as_arg uu___2 in
                 [uu___1] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu___ rng in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe] in
             let norm_f =
               let uu___ = FStar_Options.tactics_nbe () in
               if uu___
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps in
             let result =
               let uu___ = primitive_steps () in
               norm_f uu___ steps
                 proof_state.FStar_Tactics_Types.main_context tm in
             let res =
               let uu___ = FStar_Tactics_Embedding.e_result eb in
               unembed uu___ result ncb in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu___ =
                   let uu___1 =
                     let uu___2 = FStar_Syntax_Print.term_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu___2 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu___1) in
                 FStar_Errors.raise_error uu___
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
               let uu___ =
                 let uu___1 =
                   let uu___2 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state in
                   FStar_TypeChecker_NBETerm.as_arg uu___2 in
                 [uu___1] in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu___ in
             let res =
               let uu___ = FStar_Tactics_Embedding.e_result_nbe eb in
               FStar_TypeChecker_NBETerm.unembed uu___ cb result in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b1, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.ret b1)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (e, ps)) ->
                 let uu___ = FStar_Tactics_Monad.set ps in
                 FStar_Tactics_Monad.bind uu___
                   (fun uu___1 -> FStar_Tactics_Monad.traise e)
             | FStar_Pervasives_Native.None ->
                 let uu___ =
                   let uu___1 =
                     let uu___2 =
                       FStar_TypeChecker_NBETerm.t_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu___2 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu___1) in
                 FStar_Errors.raise_error uu___
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
              let uu___ =
                let uu___1 = FStar_Syntax_Syntax.as_arg x_tm in [uu___1] in
              FStar_Syntax_Syntax.mk_Tm_app f uu___ rng in
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
              let uu___ =
                let uu___1 = FStar_TypeChecker_NBETerm.as_arg x_tm in
                [uu___1] in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu___ in
            unembed_tactic_nbe_0 er cb app
let e_tactic_thunk :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Monad.tac FStar_Syntax_Embeddings.embedding
  =
  fun er ->
    let uu___ = FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu___1 ->
         fun uu___2 ->
           fun uu___3 ->
             fun uu___4 -> failwith "Impossible: embedding tactic (thunk)?")
      (fun t ->
         fun w ->
           fun cb ->
             let uu___1 =
               let uu___2 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb in
               uu___2 () in
             FStar_Pervasives_Native.Some uu___1) uu___
let e_tactic_nbe_thunk :
  'r .
    'r FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_Tactics_Monad.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er ->
    let uu___ =
      FStar_TypeChecker_NBETerm.mk_t
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
    let uu___1 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb ->
         fun uu___2 -> failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb ->
         fun t ->
           let uu___2 =
             let uu___3 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t in
             uu___3 () in
           FStar_Pervasives_Native.Some uu___2) uu___ uu___1
let e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea ->
    fun er ->
      let uu___ =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu___1 ->
           fun uu___2 ->
             fun uu___3 ->
               fun uu___4 -> failwith "Impossible: embedding tactic (1)?")
        (fun t ->
           fun w ->
             fun cb ->
               let uu___1 = unembed_tactic_1 ea er t cb in
               FStar_Pervasives_Native.Some uu___1) uu___
let e_tactic_nbe_1 :
  'a 'r .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'r FStar_TypeChecker_NBETerm.embedding ->
        ('a -> 'r FStar_Tactics_Monad.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea ->
    fun er ->
      let uu___ =
        FStar_TypeChecker_NBETerm.mk_t
          (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit) in
      let uu___1 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb ->
           fun uu___2 -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb ->
           fun t ->
             let uu___2 = unembed_tactic_nbe_1 ea er cb t in
             FStar_Pervasives_Native.Some uu___2) uu___ uu___1
let (uu___143 : unit) =
  let uu___ =
    let uu___1 =
      let uu___2 =
        mk_total_step_1'_psc Prims.int_zero "tracepoint"
          FStar_Tactics_Types.tracepoint_with_psc
          FStar_Tactics_Embedding.e_proofstate FStar_Syntax_Embeddings.e_bool
          FStar_Tactics_Types.tracepoint_with_psc
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_bool in
      let uu___3 =
        let uu___4 =
          mk_total_step_2' Prims.int_zero "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe in
        let uu___5 =
          let uu___6 =
            mk_total_step_1' Prims.int_zero "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe in
          let uu___7 =
            let uu___8 =
              mk_total_step_1' Prims.int_zero "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe in
            let uu___9 =
              let uu___10 =
                let uu___11 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal in
                let uu___12 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe in
                mk_total_step_1' Prims.int_zero "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu___11
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate_nbe uu___12 in
              let uu___11 =
                let uu___12 =
                  let uu___13 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal in
                  let uu___14 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe in
                  mk_total_step_1' Prims.int_zero "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu___13
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate_nbe uu___14 in
                let uu___13 =
                  let uu___14 =
                    mk_total_step_1' Prims.int_zero "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env in
                  let uu___15 =
                    let uu___16 =
                      mk_total_step_1' Prims.int_zero "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term in
                    let uu___17 =
                      let uu___18 =
                        mk_total_step_1' Prims.int_zero "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term in
                      let uu___19 =
                        let uu___20 =
                          mk_total_step_1' Prims.int_zero "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool in
                        let uu___21 =
                          let uu___22 =
                            mk_total_step_1' Prims.int_zero "get_label"
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal
                              FStar_Syntax_Embeddings.e_string
                              FStar_Tactics_Types.get_label
                              FStar_Tactics_Embedding.e_goal_nbe
                              FStar_TypeChecker_NBETerm.e_string in
                          let uu___23 =
                            let uu___24 =
                              mk_total_step_2' Prims.int_zero "set_label"
                                FStar_Tactics_Types.set_label
                                FStar_Syntax_Embeddings.e_string
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Embedding.e_goal
                                FStar_Tactics_Types.set_label
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_Tactics_Embedding.e_goal_nbe
                                FStar_Tactics_Embedding.e_goal_nbe in
                            let uu___25 =
                              let uu___26 =
                                let uu___27 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Tactics_Embedding.e_goal in
                                let uu___28 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_Tactics_Embedding.e_goal_nbe in
                                FStar_Tactics_InterpFuns.mk_tac_step_1
                                  Prims.int_zero "set_goals"
                                  FStar_Tactics_Monad.set_goals uu___27
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Monad.set_goals uu___28
                                  FStar_TypeChecker_NBETerm.e_unit in
                              let uu___27 =
                                let uu___28 =
                                  let uu___29 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal in
                                  let uu___30 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe in
                                  FStar_Tactics_InterpFuns.mk_tac_step_1
                                    Prims.int_zero "set_smt_goals"
                                    FStar_Tactics_Monad.set_smt_goals uu___29
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Monad.set_smt_goals uu___30
                                    FStar_TypeChecker_NBETerm.e_unit in
                                let uu___29 =
                                  let uu___30 =
                                    let uu___31 =
                                      e_tactic_thunk
                                        FStar_Syntax_Embeddings.e_any in
                                    let uu___32 =
                                      FStar_Syntax_Embeddings.e_either
                                        FStar_Tactics_Embedding.e_exn
                                        FStar_Syntax_Embeddings.e_any in
                                    let uu___33 =
                                      e_tactic_nbe_thunk
                                        FStar_TypeChecker_NBETerm.e_any in
                                    let uu___34 =
                                      FStar_TypeChecker_NBETerm.e_either
                                        FStar_Tactics_Embedding.e_exn_nbe
                                        FStar_TypeChecker_NBETerm.e_any in
                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                      Prims.int_one "catch"
                                      (fun uu___35 ->
                                         FStar_Tactics_Monad.catch)
                                      FStar_Syntax_Embeddings.e_any uu___31
                                      uu___32
                                      (fun uu___35 ->
                                         FStar_Tactics_Monad.catch)
                                      FStar_TypeChecker_NBETerm.e_any uu___33
                                      uu___34 in
                                  let uu___31 =
                                    let uu___32 =
                                      let uu___33 =
                                        e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu___34 =
                                        FStar_Syntax_Embeddings.e_either
                                          FStar_Tactics_Embedding.e_exn
                                          FStar_Syntax_Embeddings.e_any in
                                      let uu___35 =
                                        e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any in
                                      let uu___36 =
                                        FStar_TypeChecker_NBETerm.e_either
                                          FStar_Tactics_Embedding.e_exn_nbe
                                          FStar_TypeChecker_NBETerm.e_any in
                                      FStar_Tactics_InterpFuns.mk_tac_step_2
                                        Prims.int_one "recover"
                                        (fun uu___37 ->
                                           FStar_Tactics_Monad.recover)
                                        FStar_Syntax_Embeddings.e_any uu___33
                                        uu___34
                                        (fun uu___37 ->
                                           FStar_Tactics_Monad.recover)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu___35 uu___36 in
                                    let uu___33 =
                                      let uu___34 =
                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                          Prims.int_zero "intro"
                                          FStar_Tactics_Basic.intro
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Reflection_Embeddings.e_binder
                                          FStar_Tactics_Basic.intro
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_Reflection_NBEEmbeddings.e_binder in
                                      let uu___35 =
                                        let uu___36 =
                                          let uu___37 =
                                            FStar_Syntax_Embeddings.e_tuple2
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Reflection_Embeddings.e_binder in
                                          let uu___38 =
                                            FStar_TypeChecker_NBETerm.e_tuple2
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                              FStar_Reflection_NBEEmbeddings.e_binder in
                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                            Prims.int_zero "intro_rec"
                                            FStar_Tactics_Basic.intro_rec
                                            FStar_Syntax_Embeddings.e_unit
                                            uu___37
                                            FStar_Tactics_Basic.intro_rec
                                            FStar_TypeChecker_NBETerm.e_unit
                                            uu___38 in
                                        let uu___37 =
                                          let uu___38 =
                                            let uu___39 =
                                              FStar_Syntax_Embeddings.e_list
                                                FStar_Syntax_Embeddings.e_norm_step in
                                            let uu___40 =
                                              FStar_TypeChecker_NBETerm.e_list
                                                FStar_TypeChecker_NBETerm.e_norm_step in
                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                              Prims.int_zero "norm"
                                              FStar_Tactics_Basic.norm
                                              uu___39
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Tactics_Basic.norm
                                              uu___40
                                              FStar_TypeChecker_NBETerm.e_unit in
                                          let uu___39 =
                                            let uu___40 =
                                              let uu___41 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_norm_step in
                                              let uu___42 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_norm_step in
                                              FStar_Tactics_InterpFuns.mk_tac_step_3
                                                Prims.int_zero
                                                "norm_term_env"
                                                FStar_Tactics_Basic.norm_term_env
                                                FStar_Reflection_Embeddings.e_env
                                                uu___41
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Tactics_Basic.norm_term_env
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                uu___42
                                                FStar_Reflection_NBEEmbeddings.e_term
                                                FStar_Reflection_NBEEmbeddings.e_term in
                                            let uu___41 =
                                              let uu___42 =
                                                let uu___43 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step in
                                                let uu___44 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step in
                                                FStar_Tactics_InterpFuns.mk_tac_step_2
                                                  Prims.int_zero
                                                  "norm_binder_type"
                                                  FStar_Tactics_Basic.norm_binder_type
                                                  uu___43
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm_binder_type
                                                  uu___44
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_TypeChecker_NBETerm.e_unit in
                                              let uu___43 =
                                                let uu___44 =
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
                                                let uu___45 =
                                                  let uu___46 =
                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                      Prims.int_zero
                                                      "binder_retype"
                                                      FStar_Tactics_Basic.binder_retype
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.binder_retype
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit in
                                                  let uu___47 =
                                                    let uu___48 =
                                                      FStar_Tactics_InterpFuns.mk_tac_step_1
                                                        Prims.int_zero
                                                        "revert"
                                                        FStar_Tactics_Basic.revert
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.revert
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                        FStar_TypeChecker_NBETerm.e_unit in
                                                    let uu___49 =
                                                      let uu___50 =
                                                        FStar_Tactics_InterpFuns.mk_tac_step_1
                                                          Prims.int_zero
                                                          "clear_top"
                                                          FStar_Tactics_Basic.clear_top
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.clear_top
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit in
                                                      let uu___51 =
                                                        let uu___52 =
                                                          FStar_Tactics_InterpFuns.mk_tac_step_1
                                                            Prims.int_zero
                                                            "clear"
                                                            FStar_Tactics_Basic.clear
                                                            FStar_Reflection_Embeddings.e_binder
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.clear
                                                            FStar_Reflection_NBEEmbeddings.e_binder
                                                            FStar_TypeChecker_NBETerm.e_unit in
                                                        let uu___53 =
                                                          let uu___54 =
                                                            FStar_Tactics_InterpFuns.mk_tac_step_1
                                                              Prims.int_zero
                                                              "rewrite"
                                                              FStar_Tactics_Basic.rewrite
                                                              FStar_Reflection_Embeddings.e_binder
                                                              FStar_Syntax_Embeddings.e_unit
                                                              FStar_Tactics_Basic.rewrite
                                                              FStar_Reflection_NBEEmbeddings.e_binder
                                                              FStar_TypeChecker_NBETerm.e_unit in
                                                          let uu___55 =
                                                            let uu___56 =
                                                              FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                Prims.int_zero
                                                                "refine_intro"
                                                                FStar_Tactics_Basic.refine_intro
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.refine_intro
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                                FStar_TypeChecker_NBETerm.e_unit in
                                                            let uu___57 =
                                                              let uu___58 =
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
                                                              let uu___59 =
                                                                let uu___60 =
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
                                                                let uu___61 =
                                                                  let uu___62
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
                                                                  let uu___63
                                                                    =
                                                                    let uu___64
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
                                                                    let uu___65
                                                                    =
                                                                    let uu___66
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
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
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
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
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
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu___73
                                                                    ->
                                                                    fun
                                                                    uu___74
                                                                    ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
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
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
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
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
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
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
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
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
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
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
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
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "dump_uvars_of"
                                                                    FStar_Tactics_Basic.dump_uvars_of
                                                                    FStar_Tactics_Embedding.e_goal
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dump_uvars_of
                                                                    FStar_Tactics_Embedding.e_goal_nbe
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu___90 in
                                                                    let uu___90
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit in
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_Tactics_Embedding.e_ctrl_flag_nbe in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu___92 in
                                                                    let uu___92
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "ctrl_rewrite"
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu___89
                                                                    uu___90
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_CtrlRewrite.ctrl_rewrite
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu___91
                                                                    uu___92
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_trefl"
                                                                    FStar_Tactics_Basic.t_trefl
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_trefl
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
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
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
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
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
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
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu___100 in
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu___101 in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_zero
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu___99
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu___100 in
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
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
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
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
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
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
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
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
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
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
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term in
                                                                    let uu___112
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_zero
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu___111
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu___112
                                                                    FStar_Reflection_NBEEmbeddings.e_term in
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
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
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "unify_guard_env"
                                                                    FStar_Tactics_Basic.unify_guard_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.unify_guard_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_bool in
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
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
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    let uu___119
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string in
                                                                    let uu___120
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_3
                                                                    Prims.int_zero
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu___119
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu___120
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string in
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
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
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
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
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
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
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
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
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
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
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_2
                                                                    Prims.int_one
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu___131
                                                                    ->
                                                                    fun
                                                                    uu___132
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any in
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
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
                                                                    uu___133
                                                                    ->
                                                                    fun
                                                                    uu___134
                                                                    ->
                                                                    fun
                                                                    uu___135
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "set_urgency"
                                                                    FStar_Tactics_Basic.set_urgency
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_urgency
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mk_tac_step_1
                                                                    Prims.int_one
                                                                    "t_commute_applied_match"
                                                                    FStar_Tactics_Basic.t_commute_applied_match
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.t_commute_applied_match
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit in
                                                                    [uu___136] in
                                                                    uu___134
                                                                    ::
                                                                    uu___135 in
                                                                    uu___132
                                                                    ::
                                                                    uu___133 in
                                                                    uu___130
                                                                    ::
                                                                    uu___131 in
                                                                    uu___128
                                                                    ::
                                                                    uu___129 in
                                                                    uu___126
                                                                    ::
                                                                    uu___127 in
                                                                    uu___124
                                                                    ::
                                                                    uu___125 in
                                                                    uu___122
                                                                    ::
                                                                    uu___123 in
                                                                    uu___120
                                                                    ::
                                                                    uu___121 in
                                                                    uu___118
                                                                    ::
                                                                    uu___119 in
                                                                    uu___116
                                                                    ::
                                                                    uu___117 in
                                                                    uu___114
                                                                    ::
                                                                    uu___115 in
                                                                    uu___112
                                                                    ::
                                                                    uu___113 in
                                                                    uu___110
                                                                    ::
                                                                    uu___111 in
                                                                    uu___108
                                                                    ::
                                                                    uu___109 in
                                                                    uu___106
                                                                    ::
                                                                    uu___107 in
                                                                    uu___104
                                                                    ::
                                                                    uu___105 in
                                                                    uu___102
                                                                    ::
                                                                    uu___103 in
                                                                    uu___100
                                                                    ::
                                                                    uu___101 in
                                                                    uu___98
                                                                    ::
                                                                    uu___99 in
                                                                    uu___96
                                                                    ::
                                                                    uu___97 in
                                                                    uu___94
                                                                    ::
                                                                    uu___95 in
                                                                    uu___92
                                                                    ::
                                                                    uu___93 in
                                                                    uu___90
                                                                    ::
                                                                    uu___91 in
                                                                    uu___88
                                                                    ::
                                                                    uu___89 in
                                                                    uu___86
                                                                    ::
                                                                    uu___87 in
                                                                    uu___84
                                                                    ::
                                                                    uu___85 in
                                                                    uu___82
                                                                    ::
                                                                    uu___83 in
                                                                    uu___80
                                                                    ::
                                                                    uu___81 in
                                                                    uu___78
                                                                    ::
                                                                    uu___79 in
                                                                    uu___76
                                                                    ::
                                                                    uu___77 in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                    uu___64
                                                                    ::
                                                                    uu___65 in
                                                                  uu___62 ::
                                                                    uu___63 in
                                                                uu___60 ::
                                                                  uu___61 in
                                                              uu___58 ::
                                                                uu___59 in
                                                            uu___56 ::
                                                              uu___57 in
                                                          uu___54 :: uu___55 in
                                                        uu___52 :: uu___53 in
                                                      uu___50 :: uu___51 in
                                                    uu___48 :: uu___49 in
                                                  uu___46 :: uu___47 in
                                                uu___44 :: uu___45 in
                                              uu___42 :: uu___43 in
                                            uu___40 :: uu___41 in
                                          uu___38 :: uu___39 in
                                        uu___36 :: uu___37 in
                                      uu___34 :: uu___35 in
                                    uu___32 :: uu___33 in
                                  uu___30 :: uu___31 in
                                uu___28 :: uu___29 in
                              uu___26 :: uu___27 in
                            uu___24 :: uu___25 in
                          uu___22 :: uu___23 in
                        uu___20 :: uu___21 in
                      uu___18 :: uu___19 in
                    uu___16 :: uu___17 in
                  uu___14 :: uu___15 in
                uu___12 :: uu___13 in
              uu___10 :: uu___11 in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    FStar_All.pipe_left (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
      uu___1 in
  FStar_ST.op_Colon_Equals __primitive_steps_ref uu___

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
                 let uu___ =
                   let uu___1 = FStar_Syntax_Syntax.as_arg x_tm in [uu___1] in
                 FStar_Syntax_Syntax.mk_Tm_app f uu___ rng in
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
      let em uu___ uu___1 uu___2 uu___3 =
        failwith "Impossible: embedding tactic (1)?" in
      let un t0 w n =
        let uu___ = unembed_tactic_1_alt ea er t0 n in
        match uu___ with
        | FStar_Pervasives_Native.Some f ->
            FStar_Pervasives_Native.Some
              ((fun x -> let uu___1 = f x in FStar_Tactics_Monad.run uu___1))
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
      let uu___ =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit in
      FStar_Syntax_Embeddings.mk_emb em un uu___
let (report_implicits :
  FStar_Range.range -> FStar_TypeChecker_Env.implicits -> unit) =
  fun rng ->
    fun is ->
      FStar_All.pipe_right is
        (FStar_List.iter
           (fun imp ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStar_Syntax_Print.uvar_to_string
                      (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                  let uu___4 =
                    FStar_Syntax_Print.term_to_string
                      (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
                  FStar_Util.format3
                    "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                    uu___3 uu___4 imp.FStar_TypeChecker_Common.imp_reason in
                (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
                  uu___2) in
              FStar_Errors.log_issue rng uu___1));
      FStar_Errors.stop_if_err ()
let run_tactic_on_ps' :
  'a 'b .
    FStar_Range.range ->
      FStar_Range.range ->
        Prims.bool ->
          'a FStar_Syntax_Embeddings.embedding ->
            'a ->
              'b FStar_Syntax_Embeddings.embedding ->
                FStar_Syntax_Syntax.term ->
                  FStar_Tactics_Types.proofstate ->
                    (FStar_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_call ->
    fun rng_goal ->
      fun background ->
        fun e_arg ->
          fun arg ->
            fun e_res ->
              fun tactic ->
                fun ps ->
                  let env = ps.FStar_Tactics_Types.main_context in
                  (let uu___1 = FStar_ST.op_Bang tacdbg in
                   if uu___1
                   then
                     let uu___2 = FStar_Syntax_Print.term_to_string tactic in
                     FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu___2
                   else ());
                  (let uu___1 =
                     let uu___2 = FStar_Syntax_Embeddings.type_of e_arg in
                     let uu___3 = FStar_Syntax_Embeddings.type_of e_res in
                     FStar_TypeChecker_TcTerm.tc_tactic uu___2 uu___3 env
                       tactic in
                   match uu___1 with
                   | (uu___2, uu___3, g) ->
                       ((let uu___5 = FStar_ST.op_Bang tacdbg in
                         if uu___5 then FStar_Util.print_string "}\n" else ());
                        FStar_TypeChecker_Rel.force_trivial_guard env g;
                        FStar_Errors.stop_if_err ();
                        (let tau =
                           unembed_tactic_1 e_arg e_res tactic
                             FStar_Syntax_Embeddings.id_norm_cb in
                         let uu___7 =
                           FStar_Util.record_time
                             (fun uu___8 ->
                                let uu___9 = tau arg in
                                FStar_Tactics_Monad.run_safe uu___9 ps) in
                         match uu___7 with
                         | (res, ms) ->
                             ((let uu___9 = FStar_ST.op_Bang tacdbg in
                               if uu___9
                               then FStar_Util.print_string "}\n"
                               else ());
                              (let uu___10 =
                                 (FStar_ST.op_Bang tacdbg) ||
                                   (FStar_Options.tactics_info ()) in
                               if uu___10
                               then
                                 let uu___11 =
                                   FStar_Syntax_Print.term_to_string tactic in
                                 let uu___12 = FStar_Util.string_of_int ms in
                                 let uu___13 =
                                   FStar_Syntax_Print.lid_to_string
                                     env.FStar_TypeChecker_Env.curmodule in
                                 FStar_Util.print3
                                   "Tactic %s ran in %s ms (%s)\n" uu___11
                                   uu___12 uu___13
                               else ());
                              (match res with
                               | FStar_Tactics_Result.Success (ret, ps1) ->
                                   (FStar_List.iter
                                      (fun g1 ->
                                         let uu___11 =
                                           FStar_Tactics_Types.is_irrelevant
                                             g1 in
                                         if uu___11
                                         then
                                           let uu___12 =
                                             let uu___13 =
                                               FStar_Tactics_Types.goal_env
                                                 g1 in
                                             let uu___14 =
                                               FStar_Tactics_Types.goal_witness
                                                 g1 in
                                             FStar_TypeChecker_Rel.teq_nosmt_force
                                               uu___13 uu___14
                                               FStar_Syntax_Util.exp_unit in
                                           (if uu___12
                                            then ()
                                            else
                                              (let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 =
                                                     FStar_Tactics_Types.goal_witness
                                                       g1 in
                                                   FStar_Syntax_Print.term_to_string
                                                     uu___16 in
                                                 FStar_Util.format1
                                                   "Irrelevant tactic witness does not unify with (): %s"
                                                   uu___15 in
                                               failwith uu___14))
                                         else ())
                                      (FStar_List.append
                                         ps1.FStar_Tactics_Types.goals
                                         ps1.FStar_Tactics_Types.smt_goals);
                                    (let uu___12 = FStar_ST.op_Bang tacdbg in
                                     if uu___12
                                     then
                                       let uu___13 =
                                         FStar_Common.string_of_list
                                           (fun imp ->
                                              FStar_Syntax_Print.ctx_uvar_to_string
                                                imp.FStar_TypeChecker_Common.imp_uvar)
                                           ps1.FStar_Tactics_Types.all_implicits in
                                       FStar_Util.print1
                                         "About to check tactic implicits: %s\n"
                                         uu___13
                                     else ());
                                    (let g1 =
                                       let uu___12 =
                                         FStar_TypeChecker_Env.trivial_guard in
                                       {
                                         FStar_TypeChecker_Common.guard_f =
                                           (uu___12.FStar_TypeChecker_Common.guard_f);
                                         FStar_TypeChecker_Common.deferred_to_tac
                                           =
                                           (uu___12.FStar_TypeChecker_Common.deferred_to_tac);
                                         FStar_TypeChecker_Common.deferred =
                                           (uu___12.FStar_TypeChecker_Common.deferred);
                                         FStar_TypeChecker_Common.univ_ineqs
                                           =
                                           (uu___12.FStar_TypeChecker_Common.univ_ineqs);
                                         FStar_TypeChecker_Common.implicits =
                                           (ps1.FStar_Tactics_Types.all_implicits)
                                       } in
                                     let g2 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env g1 in
                                     (let uu___13 = FStar_ST.op_Bang tacdbg in
                                      if uu___13
                                      then
                                        let uu___14 =
                                          FStar_Util.string_of_int
                                            (FStar_List.length
                                               ps1.FStar_Tactics_Types.all_implicits) in
                                        let uu___15 =
                                          FStar_Common.string_of_list
                                            (fun imp ->
                                               FStar_Syntax_Print.ctx_uvar_to_string
                                                 imp.FStar_TypeChecker_Common.imp_uvar)
                                            ps1.FStar_Tactics_Types.all_implicits in
                                        FStar_Util.print2
                                          "Checked %s implicits (1): %s\n"
                                          uu___14 uu___15
                                      else ());
                                     (let g3 =
                                        FStar_TypeChecker_Rel.resolve_implicits_tac
                                          env g2 in
                                      (let uu___14 = FStar_ST.op_Bang tacdbg in
                                       if uu___14
                                       then
                                         let uu___15 =
                                           FStar_Util.string_of_int
                                             (FStar_List.length
                                                ps1.FStar_Tactics_Types.all_implicits) in
                                         let uu___16 =
                                           FStar_Common.string_of_list
                                             (fun imp ->
                                                FStar_Syntax_Print.ctx_uvar_to_string
                                                  imp.FStar_TypeChecker_Common.imp_uvar)
                                             ps1.FStar_Tactics_Types.all_implicits in
                                         FStar_Util.print2
                                           "Checked %s implicits (2): %s\n"
                                           uu___15 uu___16
                                       else ());
                                      report_implicits rng_goal
                                        g3.FStar_TypeChecker_Common.implicits;
                                      (let uu___16 = FStar_ST.op_Bang tacdbg in
                                       if uu___16
                                       then
                                         let uu___17 =
                                           let uu___18 =
                                             FStar_TypeChecker_Cfg.psc_subst
                                               ps1.FStar_Tactics_Types.psc in
                                           FStar_Tactics_Types.subst_proof_state
                                             uu___18 ps1 in
                                         FStar_Tactics_Printing.do_dump_proofstate
                                           uu___17 "at the finish line"
                                       else ());
                                      ((FStar_List.append
                                          ps1.FStar_Tactics_Types.goals
                                          ps1.FStar_Tactics_Types.smt_goals),
                                        ret))))
                               | FStar_Tactics_Result.Failed (e, ps1) ->
                                   ((let uu___11 =
                                       let uu___12 =
                                         FStar_TypeChecker_Cfg.psc_subst
                                           ps1.FStar_Tactics_Types.psc in
                                       FStar_Tactics_Types.subst_proof_state
                                         uu___12 ps1 in
                                     FStar_Tactics_Printing.do_dump_proofstate
                                       uu___11 "at the time of failure");
                                    (let texn_to_string e1 =
                                       match e1 with
                                       | FStar_Tactics_Common.TacticFailure s
                                           -> s
                                       | FStar_Tactics_Common.EExn t ->
                                           let uu___11 =
                                             FStar_Syntax_Print.term_to_string
                                               t in
                                           Prims.op_Hat
                                             "uncaught exception: " uu___11
                                       | e2 -> FStar_Exn.raise e2 in
                                     let rng =
                                       if background
                                       then
                                         match ps1.FStar_Tactics_Types.goals
                                         with
                                         | g1::uu___11 ->
                                             (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
                                         | uu___11 -> rng_call
                                       else
                                         ps1.FStar_Tactics_Types.entry_range in
                                     let uu___11 =
                                       let uu___12 =
                                         let uu___13 = texn_to_string e in
                                         FStar_Util.format1
                                           "user tactic failed: `%s`" uu___13 in
                                       (FStar_Errors.Fatal_UserTacticFailure,
                                         uu___12) in
                                     FStar_Errors.raise_error uu___11 rng)))))))
let run_tactic_on_ps :
  'a 'b .
    FStar_Range.range ->
      FStar_Range.range ->
        Prims.bool ->
          'a FStar_Syntax_Embeddings.embedding ->
            'a ->
              'b FStar_Syntax_Embeddings.embedding ->
                FStar_Syntax_Syntax.term ->
                  FStar_Tactics_Types.proofstate ->
                    (FStar_Tactics_Types.goal Prims.list * 'b)
  =
  fun rng_call ->
    fun rng_goal ->
      fun background ->
        fun e_arg ->
          fun arg ->
            fun e_res ->
              fun tactic ->
                fun ps ->
                  let uu___ =
                    let uu___1 =
                      let uu___2 =
                        FStar_TypeChecker_Env.current_module
                          ps.FStar_Tactics_Types.main_context in
                      FStar_Ident.string_of_lid uu___2 in
                    FStar_Pervasives_Native.Some uu___1 in
                  FStar_Profiling.profile
                    (fun uu___1 ->
                       run_tactic_on_ps' rng_call rng_goal background e_arg
                         arg e_res tactic ps) uu___
                    "FStar.Tactics.Interpreter.run_tactic_on_ps"