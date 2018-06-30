open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec e_tactic_0' :
  'r .
    'r FStar_Syntax_Embeddings.embedding ->
      'r FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____146  ->
         fun uu____147  -> failwith "Impossible: embedding tactic (0)?")
      (fun w  ->
         fun t  ->
           let uu____155 = unembed_tactic_0 er t  in
           FStar_All.pipe_left
             (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____155)
      FStar_Syntax_Syntax.t_unit

and e_tactic_1 :
  'a 'r .
    'a FStar_Syntax_Embeddings.embedding ->
      'r FStar_Syntax_Embeddings.embedding ->
        ('a -> 'r FStar_Tactics_Basic.tac) FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____179  ->
           fun uu____180  -> failwith "Impossible: embedding tactic (1)?")
        (fun w  -> fun t  -> unembed_tactic_1 ea er t)
        FStar_Syntax_Syntax.t_unit

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____189  ->
    let tracepoint1 =
      let uu___345_193 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____194 = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____194;
        FStar_TypeChecker_Cfg.arity =
          (uu___345_193.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___345_193.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___345_193.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___345_193.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___345_193.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___345_193.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___345_193.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let set_proofstate_range1 =
      let uu___346_196 =
        FStar_Tactics_InterpFuns.mktot2 (Prims.parse_int "0")
          "set_proofstate_range" FStar_Tactics_Types.set_proofstate_range
          FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_range
          FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Types.set_proofstate_range
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_range
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____197 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Cfg.name = uu____197;
        FStar_TypeChecker_Cfg.arity =
          (uu___346_196.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___346_196.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___346_196.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___346_196.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___346_196.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___346_196.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___346_196.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let incr_depth1 =
      let uu___347_199 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "incr_depth"
          FStar_Tactics_Types.incr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.incr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____200 = FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____200;
        FStar_TypeChecker_Cfg.arity =
          (uu___347_199.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___347_199.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___347_199.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___347_199.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___347_199.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___347_199.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___347_199.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let decr_depth1 =
      let uu___348_202 =
        FStar_Tactics_InterpFuns.mktot1 (Prims.parse_int "0") "decr_depth"
          FStar_Tactics_Types.decr_depth FStar_Tactics_Embedding.e_proofstate
          FStar_Tactics_Embedding.e_proofstate FStar_Tactics_Types.decr_depth
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_Tactics_Embedding.e_proofstate_nbe
         in
      let uu____203 = FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"
         in
      {
        FStar_TypeChecker_Cfg.name = uu____203;
        FStar_TypeChecker_Cfg.arity =
          (uu___348_202.FStar_TypeChecker_Cfg.arity);
        FStar_TypeChecker_Cfg.univ_arity =
          (uu___348_202.FStar_TypeChecker_Cfg.univ_arity);
        FStar_TypeChecker_Cfg.auto_reflect =
          (uu___348_202.FStar_TypeChecker_Cfg.auto_reflect);
        FStar_TypeChecker_Cfg.strong_reduction_ok =
          (uu___348_202.FStar_TypeChecker_Cfg.strong_reduction_ok);
        FStar_TypeChecker_Cfg.requires_binder_substitution =
          (uu___348_202.FStar_TypeChecker_Cfg.requires_binder_substitution);
        FStar_TypeChecker_Cfg.interpretation =
          (uu___348_202.FStar_TypeChecker_Cfg.interpretation);
        FStar_TypeChecker_Cfg.interpretation_nbe =
          (uu___348_202.FStar_TypeChecker_Cfg.interpretation_nbe)
      }  in
    let uu____204 =
      let uu____207 =
        let uu____210 =
          let uu____213 =
            let uu____216 =
              let uu____219 =
                FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1") "fail"
                  (fun uu____221  -> FStar_Tactics_Basic.fail)
                  FStar_Syntax_Embeddings.e_any
                  FStar_Syntax_Embeddings.e_string
                  FStar_Syntax_Embeddings.e_any
                 in
              let uu____222 =
                let uu____225 =
                  FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                    "trivial" FStar_Tactics_Basic.trivial
                    FStar_Syntax_Embeddings.e_unit
                    FStar_Syntax_Embeddings.e_unit
                    FStar_Tactics_Basic.trivial
                    FStar_TypeChecker_NBETerm.e_unit
                    FStar_TypeChecker_NBETerm.e_unit
                   in
                let uu____226 =
                  let uu____229 =
                    let uu____230 = e_tactic_0' FStar_Syntax_Embeddings.e_any
                       in
                    let uu____235 =
                      FStar_Syntax_Embeddings.e_option
                        FStar_Syntax_Embeddings.e_any
                       in
                    FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                      "__trytac"
                      (fun uu____245  -> FStar_Tactics_Basic.trytac)
                      FStar_Syntax_Embeddings.e_any uu____230 uu____235
                     in
                  let uu____246 =
                    let uu____249 =
                      let uu____250 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      FStar_Tactics_InterpFuns.mktac3 (Prims.parse_int "0")
                        "norm_term_env" FStar_Tactics_Basic.norm_term_env
                        FStar_Reflection_Embeddings.e_env uu____250
                        FStar_Reflection_Embeddings.e_term
                        FStar_Reflection_Embeddings.e_term
                       in
                    let uu____257 =
                      let uu____260 =
                        let uu____261 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_norm_step
                           in
                        FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "0")
                          "norm_binder_type"
                          FStar_Tactics_Basic.norm_binder_type uu____261
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_unit
                         in
                      let uu____268 =
                        let uu____271 =
                          FStar_Tactics_InterpFuns.mktac2
                            (Prims.parse_int "0") "rename_to"
                            FStar_Tactics_Basic.rename_to
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_string
                            FStar_Syntax_Embeddings.e_unit
                           in
                        let uu____272 =
                          let uu____275 =
                            FStar_Tactics_InterpFuns.mktac2
                              (Prims.parse_int "0") "t_exact"
                              FStar_Tactics_Basic.t_exact
                              FStar_Syntax_Embeddings.e_bool
                              FStar_Reflection_Embeddings.e_term
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____276 =
                            let uu____279 =
                              FStar_Tactics_InterpFuns.mktac1
                                (Prims.parse_int "0") "apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Embeddings.e_term
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Embeddings.e_term_nbe
                                FStar_TypeChecker_NBETerm.e_unit
                               in
                            let uu____280 =
                              let uu____283 =
                                let uu____284 =
                                  e_tactic_0' FStar_Syntax_Embeddings.e_any
                                   in
                                let uu____289 =
                                  e_tactic_0' FStar_Syntax_Embeddings.e_any
                                   in
                                let uu____294 =
                                  FStar_Syntax_Embeddings.e_tuple2
                                    FStar_Syntax_Embeddings.e_any
                                    FStar_Syntax_Embeddings.e_any
                                   in
                                FStar_Tactics_InterpFuns.mktac5
                                  (Prims.parse_int "2") "__divide"
                                  (fun uu____311  ->
                                     fun uu____312  ->
                                       FStar_Tactics_Basic.divide)
                                  FStar_Syntax_Embeddings.e_any
                                  FStar_Syntax_Embeddings.e_any
                                  FStar_Syntax_Embeddings.e_int uu____284
                                  uu____289 uu____294
                                 in
                              let uu____313 =
                                let uu____316 =
                                  let uu____317 =
                                    e_tactic_0'
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____322 =
                                    e_tactic_0'
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  FStar_Tactics_InterpFuns.mktac2
                                    (Prims.parse_int "0") "__seq"
                                    FStar_Tactics_Basic.seq uu____317
                                    uu____322 FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____331 =
                                  let uu____334 =
                                    FStar_Tactics_InterpFuns.mktac2
                                      (Prims.parse_int "1") "unquote"
                                      FStar_Tactics_Basic.unquote
                                      FStar_Syntax_Embeddings.e_any
                                      FStar_Reflection_Embeddings.e_term
                                      FStar_Syntax_Embeddings.e_any
                                     in
                                  let uu____335 =
                                    let uu____338 =
                                      let uu____339 =
                                        e_tactic_0'
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      FStar_Tactics_InterpFuns.mktac2
                                        (Prims.parse_int "0") "__pointwise"
                                        FStar_Tactics_Basic.pointwise
                                        FStar_Tactics_Embedding.e_direction
                                        uu____339
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____346 =
                                      let uu____349 =
                                        let uu____350 =
                                          let uu____362 =
                                            FStar_Syntax_Embeddings.e_tuple2
                                              FStar_Syntax_Embeddings.e_bool
                                              FStar_Syntax_Embeddings.e_int
                                             in
                                          e_tactic_1
                                            FStar_Reflection_Embeddings.e_term
                                            uu____362
                                           in
                                        let uu____373 =
                                          e_tactic_0'
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        FStar_Tactics_InterpFuns.mktac2
                                          (Prims.parse_int "0")
                                          "__topdown_rewrite"
                                          FStar_Tactics_Basic.topdown_rewrite
                                          uu____350 uu____373
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____389 =
                                        let uu____392 =
                                          let uu____393 =
                                            FStar_Syntax_Embeddings.e_option
                                              FStar_Reflection_Embeddings.e_term
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            (Prims.parse_int "0") "uvar_env"
                                            FStar_Tactics_Basic.uvar_env
                                            FStar_Reflection_Embeddings.e_env
                                            uu____393
                                            FStar_Reflection_Embeddings.e_term
                                           in
                                        let uu____400 =
                                          let uu____403 =
                                            FStar_Tactics_InterpFuns.mktac3
                                              (Prims.parse_int "0")
                                              "unify_env"
                                              FStar_Tactics_Basic.unify_env
                                              FStar_Reflection_Embeddings.e_env
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_bool
                                             in
                                          let uu____404 =
                                            let uu____407 =
                                              let uu____408 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_string
                                                 in
                                              FStar_Tactics_InterpFuns.mktac3
                                                (Prims.parse_int "0")
                                                "launch_process"
                                                FStar_Tactics_Basic.launch_process
                                                FStar_Syntax_Embeddings.e_string
                                                uu____408
                                                FStar_Syntax_Embeddings.e_string
                                                FStar_Syntax_Embeddings.e_string
                                               in
                                            let uu____415 =
                                              let uu____418 =
                                                FStar_Tactics_InterpFuns.mktac2
                                                  (Prims.parse_int "0")
                                                  "fresh_bv_named"
                                                  FStar_Tactics_Basic.fresh_bv_named
                                                  FStar_Syntax_Embeddings.e_string
                                                  FStar_Reflection_Embeddings.e_term
                                                  FStar_Reflection_Embeddings.e_bv
                                                 in
                                              [uu____418]  in
                                            uu____407 :: uu____415  in
                                          uu____403 :: uu____404  in
                                        uu____392 :: uu____400  in
                                      uu____349 :: uu____389  in
                                    uu____338 :: uu____346  in
                                  uu____334 :: uu____335  in
                                uu____316 :: uu____331  in
                              uu____283 :: uu____313  in
                            uu____279 :: uu____280  in
                          uu____275 :: uu____276  in
                        uu____271 :: uu____272  in
                      uu____260 :: uu____268  in
                    uu____249 :: uu____257  in
                  uu____229 :: uu____246  in
                uu____225 :: uu____226  in
              uu____219 :: uu____222  in
            set_proofstate_range1 :: uu____216  in
          tracepoint1 :: uu____213  in
        decr_depth1 :: uu____210  in
      incr_depth1 :: uu____207  in
    FStar_List.append uu____204
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         FStar_Tactics_InterpFuns.native_tactics_steps)

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          ('Aa -> 'Ar FStar_Tactics_Basic.tac) FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        FStar_Pervasives_Native.Some
          (fun x  ->
             let rng = FStar_Range.dummyRange  in
             let x_tm = FStar_Syntax_Embeddings.embed ea rng x  in
             let app1 =
               let uu____441 =
                 let uu____446 =
                   let uu____447 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____447]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____446  in
               uu____441 FStar_Pervasives_Native.None rng  in
             unembed_tactic_0 er app1)

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
           let tm =
             let uu____495 =
               let uu____500 =
                 let uu____501 =
                   let uu____510 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____510  in
                 [uu____501]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____500  in
             uu____495 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Env.Weak;
             FStar_TypeChecker_Env.Reify;
             FStar_TypeChecker_Env.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Env.UnfoldTac;
             FStar_TypeChecker_Env.Primops;
             FStar_TypeChecker_Env.Unascribe]  in
           let norm_f =
             let uu____553 = FStar_Options.tactics_nbe ()  in
             if uu____553
             then FStar_TypeChecker_NBE.normalize_with_primitive_steps
             else FStar_TypeChecker_Normalize.normalize_with_primitive_steps
              in
           if proof_state.FStar_Tactics_Types.tac_verb_dbg
           then
             (let uu____572 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____572)
           else ();
           (let result =
              let uu____575 = primitive_steps ()  in
              norm_f uu____575 steps
                proof_state.FStar_Tactics_Types.main_context tm
               in
            if proof_state.FStar_Tactics_Types.tac_verb_dbg
            then
              (let uu____579 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____579)
            else ();
            (let res =
               let uu____586 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____586 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____599 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____599
                   (fun uu____603  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____608 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____608
                   (fun uu____612  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____615 =
                   let uu____620 =
                     let uu____621 = FStar_Syntax_Print.term_to_string result
                        in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____621
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____620)  in
                 FStar_Errors.raise_error uu____615
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____628 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
        uu____628

let report_implicits :
  'Auu____645 . 'Auu____645 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____674 =
               let uu____675 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____676 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____675 uu____676 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____674, (imp.FStar_TypeChecker_Env.imp_range))) is
         in
      FStar_Errors.add_errors errs
  
let (run_tactic_on_typ :
  FStar_Range.range ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.typ ->
            (FStar_Tactics_Basic.goal Prims.list,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2)
  =
  fun rng_tac  ->
    fun rng_goal  ->
      fun tactic  ->
        fun env  ->
          fun typ  ->
            (let uu____715 = FStar_ST.op_Bang tacdbg  in
             if uu____715
             then
               let uu____735 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____735
             else ());
            (let uu____737 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____737 with
             | (uu____750,uu____751,g) ->
                 ((let uu____754 = FStar_ST.op_Bang tacdbg  in
                   if uu____754 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                      in
                   let uu____780 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____780 with
                   | (env1,uu____794) ->
                       let env2 =
                         let uu___349_800 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___349_800.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___349_800.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___349_800.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___349_800.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___349_800.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___349_800.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___349_800.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___349_800.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___349_800.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___349_800.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___349_800.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___349_800.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___349_800.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___349_800.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___349_800.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___349_800.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___349_800.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___349_800.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___349_800.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___349_800.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___349_800.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___349_800.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___349_800.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___349_800.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___349_800.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___349_800.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___349_800.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___349_800.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___349_800.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___349_800.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___349_800.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___349_800.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___349_800.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___349_800.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___349_800.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___349_800.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___349_800.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___349_800.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___349_800.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___349_800.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___349_800.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___350_802 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___350_802.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___350_802.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___350_802.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___350_802.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___350_802.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___350_802.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___350_802.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___350_802.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___350_802.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___350_802.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___350_802.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___350_802.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___350_802.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___350_802.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___350_802.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___350_802.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___350_802.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___350_802.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___350_802.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___350_802.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___350_802.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___350_802.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___350_802.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___350_802.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___350_802.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___350_802.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___350_802.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___350_802.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___350_802.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___350_802.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___350_802.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___350_802.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___350_802.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___350_802.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___350_802.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___350_802.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___350_802.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___350_802.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___350_802.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___350_802.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___350_802.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___351_804 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___351_804.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___351_804.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___351_804.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___351_804.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___351_804.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___351_804.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___351_804.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___351_804.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___351_804.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___351_804.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___351_804.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___351_804.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___351_804.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___351_804.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___351_804.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___351_804.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___351_804.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___351_804.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___351_804.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___351_804.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___351_804.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___351_804.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___351_804.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___351_804.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___351_804.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___351_804.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___351_804.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___351_804.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___351_804.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___351_804.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___351_804.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___351_804.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___351_804.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___351_804.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___351_804.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___351_804.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___351_804.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___351_804.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___351_804.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___351_804.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___351_804.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____806 = FStar_Range.use_range rng_goal  in
                         let uu____807 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____806 uu____807  in
                       let uu____808 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____808 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____846 = FStar_ST.op_Bang tacdbg  in
                              if uu____846
                              then
                                let uu____866 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____866
                              else ());
                             (let uu____868 =
                                FStar_Util.record_time
                                  (fun uu____878  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____868 with
                              | (res,ms) ->
                                  ((let uu____892 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____892
                                    then
                                      let uu____912 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____913 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____914 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____912 uu____913 uu____914
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____922,ps1) ->
                                        ((let uu____925 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____925
                                          then
                                            let uu____945 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____945
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____952 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____952
                                              then
                                                let uu____953 =
                                                  let uu____954 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____955 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____954 uu____955
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____953
                                                 then ()
                                                 else
                                                   (let uu____957 =
                                                      let uu____958 =
                                                        let uu____959 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____959
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____958
                                                       in
                                                    failwith uu____957))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____962 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____962
                                          then
                                            let uu____982 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____982
                                          else ());
                                         (let g1 =
                                            let uu___352_987 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___352_987.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___352_987.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___352_987.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____990 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____990
                                           then
                                             let uu____1010 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print1
                                               "Checked (1) implicits: %s\n"
                                               uu____1010
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____1016 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1016
                                            then
                                              let uu____1036 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "Checked (2) implicits: %s\n"
                                                uu____1036
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____1046 =
                                            let uu____1047 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____1047 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____1046
                                            "at the time of failure");
                                         (let uu____1048 =
                                            let uu____1053 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____1053)
                                             in
                                          FStar_Errors.raise_error uu____1048
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____1065 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____1071 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____1077 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____1132 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____1172 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____1226 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____1267 . 'Auu____1267 -> 'Auu____1267 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1295 = FStar_Syntax_Util.head_and_args t  in
        match uu____1295 with
        | (hd1,args) ->
            let uu____1338 =
              let uu____1353 =
                let uu____1354 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1354.FStar_Syntax_Syntax.n  in
              (uu____1353, args)  in
            (match uu____1338 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1369))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____1432 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1432 with
                       | (gs,uu____1440) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____1447 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1447 with
                       | (gs,uu____1455) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____1498 =
                        let uu____1505 =
                          let uu____1508 =
                            let uu____1509 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____1509
                             in
                          [uu____1508]  in
                        (FStar_Syntax_Util.t_true, uu____1505)  in
                      Simplified uu____1498
                  | Both  ->
                      let uu____1520 =
                        let uu____1529 =
                          let uu____1532 =
                            let uu____1533 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____1533
                             in
                          [uu____1532]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____1529)  in
                      Dual uu____1520
                  | Neg  -> Simplified (assertion, []))
             | uu____1546 -> Unchanged t)
  
let explode :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
  
let comb1 : 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___344_1636  ->
      match uu___344_1636 with
      | Unchanged t -> let uu____1642 = f t  in Unchanged uu____1642
      | Simplified (t,gs) ->
          let uu____1649 = let uu____1656 = f t  in (uu____1656, gs)  in
          Simplified uu____1649
      | Dual (tn,tp,gs) ->
          let uu____1666 =
            let uu____1675 = f tn  in
            let uu____1676 = f tp  in (uu____1675, uu____1676, gs)  in
          Dual uu____1666
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____1739 = f t1 t2  in Unchanged uu____1739
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____1751 = let uu____1758 = f t1 t2  in (uu____1758, gs)
               in
            Simplified uu____1751
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____1772 = let uu____1779 = f t1 t2  in (uu____1779, gs)
               in
            Simplified uu____1772
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____1798 =
              let uu____1805 = f t1 t2  in
              (uu____1805, (FStar_List.append gs1 gs2))  in
            Simplified uu____1798
        | uu____1808 ->
            let uu____1817 = explode x  in
            (match uu____1817 with
             | (n1,p1,gs1) ->
                 let uu____1835 = explode y  in
                 (match uu____1835 with
                  | (n2,p2,gs2) ->
                      let uu____1853 =
                        let uu____1862 = f n1 n2  in
                        let uu____1863 = f p1 p2  in
                        (uu____1862, uu____1863, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____1853))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____1935 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____1935
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____1983  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____2025 =
              let uu____2026 = FStar_Syntax_Subst.compress t  in
              uu____2026.FStar_Syntax_Syntax.n  in
            match uu____2025 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____2038 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____2038 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____2064 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____2064 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2084;
                   FStar_Syntax_Syntax.vars = uu____2085;_},(p,uu____2087)::
                 (q,uu____2089)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2145 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2145
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____2148 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____2148 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____2162 = FStar_Syntax_Util.mk_imp l r  in
                       uu____2162.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2166;
                   FStar_Syntax_Syntax.vars = uu____2167;_},(p,uu____2169)::
                 (q,uu____2171)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____2227 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2227
                   in
                let xq =
                  let uu____2229 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2229
                   in
                let r1 =
                  let uu____2231 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____2231 p  in
                let r2 =
                  let uu____2233 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____2233 q  in
                (match (r1, r2) with
                 | (Unchanged uu____2240,Unchanged uu____2241) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____2259 = FStar_Syntax_Util.mk_iff l r  in
                            uu____2259.FStar_Syntax_Syntax.n) r1 r2
                 | uu____2262 ->
                     let uu____2271 = explode r1  in
                     (match uu____2271 with
                      | (pn,pp,gs1) ->
                          let uu____2289 = explode r2  in
                          (match uu____2289 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____2310 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____2313 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____2310
                                   uu____2313
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____2377  ->
                       fun r  ->
                         match uu____2377 with
                         | (a,q) ->
                             let r' = traverse f pol e a  in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure [])
                   in
                comb2
                  (fun hd2  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd2, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____2529 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____2529 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____2569  ->
                            match uu____2569 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____2591 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___353_2623 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___353_2623.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___353_2623.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____2591 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____2651 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____2651.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____2697 = traverse f pol e t1  in
                let uu____2702 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____2702 uu____2697
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___354_2742 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___354_2742.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___354_2742.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____2749 =
                f pol e
                  (let uu___355_2753 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___355_2753.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___355_2753.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____2749
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___356_2763 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___356_2763.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___356_2763.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____2764 = explode rp  in
              (match uu____2764 with
               | (uu____2773,p',gs') ->
                   Dual
                     ((let uu___357_2783 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___357_2783.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___357_2783.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
  
let (getprop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Weak;
          FStar_TypeChecker_Env.HNF;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant] e t
         in
      FStar_Syntax_Util.un_squash tn
  
let (preprocess :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun env  ->
    fun goal  ->
      (let uu____2826 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____2826);
      (let uu____2847 = FStar_ST.op_Bang tacdbg  in
       if uu____2847
       then
         let uu____2867 =
           let uu____2868 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____2868
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____2869 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____2867
           uu____2869
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____2898 =
         let uu____2907 = traverse by_tactic_interp Pos env goal  in
         match uu____2907 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____2931 -> failwith "no"  in
       match uu____2898 with
       | (t',gs) ->
           ((let uu____2959 = FStar_ST.op_Bang tacdbg  in
             if uu____2959
             then
               let uu____2979 =
                 let uu____2980 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____2980
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____2981 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____2979 uu____2981
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3029  ->
                    fun g  ->
                      match uu____3029 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3074 =
                              let uu____3077 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____3078 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____3077 uu____3078  in
                            match uu____3074 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3079 =
                                  let uu____3084 =
                                    let uu____3085 =
                                      let uu____3086 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____3086
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____3085
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____3084)
                                   in
                                FStar_Errors.raise_error uu____3079
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____3089 = FStar_ST.op_Bang tacdbg  in
                            if uu____3089
                            then
                              let uu____3109 = FStar_Util.string_of_int n1
                                 in
                              let uu____3110 =
                                let uu____3111 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____3111
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3109 uu____3110
                            else ());
                           (let gt' =
                              let uu____3114 =
                                let uu____3115 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____3115
                                 in
                              FStar_TypeChecker_Util.label uu____3114
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____3116 =
                              let uu____3125 =
                                let uu____3132 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____3132, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____3125 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____3116)))) s
                 gs
                in
             let uu____3147 = s1  in
             match uu____3147 with
             | (uu____3168,gs1) ->
                 let uu____3186 =
                   let uu____3193 = FStar_Options.peek ()  in
                   (env, t', uu____3193)  in
                 uu____3186 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____3206 =
        let uu____3207 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____3207  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3206 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____3208 =
      let uu____3213 =
        let uu____3214 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____3223 =
          let uu____3234 = FStar_Syntax_Syntax.as_arg a  in [uu____3234]  in
        uu____3214 :: uu____3223  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3213  in
    uu____3208 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
let (synthesize :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        if env.FStar_TypeChecker_Env.nosynth
        then
          let uu____3284 =
            let uu____3289 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____3290 =
              let uu____3291 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3291]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____3289 uu____3290  in
          uu____3284 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____3320 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____3320);
           (let uu____3340 =
              let uu____3347 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____3347 env typ
               in
            match uu____3340 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____3361 =
                        let uu____3364 = FStar_Tactics_Types.goal_env g  in
                        let uu____3365 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____3364 uu____3365  in
                      match uu____3361 with
                      | FStar_Pervasives_Native.Some vc ->
                          let guard =
                            {
                              FStar_TypeChecker_Env.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Env.deferred = [];
                              FStar_TypeChecker_Env.univ_ineqs = ([], []);
                              FStar_TypeChecker_Env.implicits = []
                            }  in
                          let uu____3376 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____3376 guard
                      | FStar_Pervasives_Native.None  ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                              "synthesis left open goals")
                            typ.FStar_Syntax_Syntax.pos) gs;
                 w)))
  
let (splice :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun tau  ->
      if env.FStar_TypeChecker_Env.nosynth
      then []
      else
        ((let uu____3393 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____3393);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____3414 =
            let uu____3421 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____3421 env typ
             in
          match uu____3414 with
          | (gs,w) ->
              ((let uu____3431 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____3435 =
                         let uu____3436 =
                           let uu____3439 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____3440 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____3439 uu____3440  in
                         FStar_Option.isSome uu____3436  in
                       Prims.op_Negation uu____3435) gs
                   in
                if uu____3431
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let w1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Weak;
                    FStar_TypeChecker_Env.HNF;
                    FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.Unascribe;
                    FStar_TypeChecker_Env.Unmeta] env w
                   in
                (let uu____3444 = FStar_ST.op_Bang tacdbg  in
                 if uu____3444
                 then
                   let uu____3464 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____3464
                 else ());
                (let uu____3466 =
                   let uu____3471 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Syntax_Embeddings.unembed uu____3471 w1  in
                 match uu____3466 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  