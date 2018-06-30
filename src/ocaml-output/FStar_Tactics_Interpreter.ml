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
          FStar_Syntax_Embeddings.e_unit
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
          FStar_Tactics_Embedding.e_proofstate
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
          FStar_Tactics_Embedding.e_proofstate
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
                FStar_Tactics_InterpFuns.mktot2 (Prims.parse_int "0")
                  "push_binder"
                  (fun env  ->
                     fun b  -> FStar_TypeChecker_Env.push_binders env [b])
                  FStar_Reflection_Embeddings.e_env
                  FStar_Reflection_Embeddings.e_binder
                  FStar_Reflection_Embeddings.e_env
                 in
              let uu____248 =
                let uu____251 =
                  FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                    "fail" (fun uu____253  -> FStar_Tactics_Basic.fail)
                    FStar_Syntax_Embeddings.e_any
                    FStar_Syntax_Embeddings.e_string
                    FStar_Syntax_Embeddings.e_any
                   in
                let uu____254 =
                  let uu____257 =
                    FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                      "trivial" FStar_Tactics_Basic.trivial
                      FStar_Syntax_Embeddings.e_unit
                      FStar_Syntax_Embeddings.e_unit
                     in
                  let uu____258 =
                    let uu____261 =
                      let uu____262 =
                        e_tactic_0' FStar_Syntax_Embeddings.e_any  in
                      let uu____267 =
                        FStar_Syntax_Embeddings.e_option
                          FStar_Syntax_Embeddings.e_any
                         in
                      FStar_Tactics_InterpFuns.mktac2 (Prims.parse_int "1")
                        "__trytac"
                        (fun uu____277  -> FStar_Tactics_Basic.trytac)
                        FStar_Syntax_Embeddings.e_any uu____262 uu____267
                       in
                    let uu____278 =
                      let uu____281 =
                        FStar_Tactics_InterpFuns.mktac1 (Prims.parse_int "0")
                          "intro" FStar_Tactics_Basic.intro
                          FStar_Syntax_Embeddings.e_unit
                          FStar_Reflection_Embeddings.e_binder
                         in
                      let uu____282 =
                        let uu____285 =
                          let uu____286 =
                            FStar_Syntax_Embeddings.e_tuple2
                              FStar_Reflection_Embeddings.e_binder
                              FStar_Reflection_Embeddings.e_binder
                             in
                          FStar_Tactics_InterpFuns.mktac1
                            (Prims.parse_int "0") "intro_rec"
                            FStar_Tactics_Basic.intro_rec
                            FStar_Syntax_Embeddings.e_unit uu____286
                           in
                        let uu____297 =
                          let uu____300 =
                            let uu____301 =
                              FStar_Syntax_Embeddings.e_list
                                FStar_Syntax_Embeddings.e_norm_step
                               in
                            FStar_Tactics_InterpFuns.mktac1
                              (Prims.parse_int "0") "norm"
                              FStar_Tactics_Basic.norm uu____301
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____308 =
                            let uu____311 =
                              let uu____312 =
                                FStar_Syntax_Embeddings.e_list
                                  FStar_Syntax_Embeddings.e_norm_step
                                 in
                              FStar_Tactics_InterpFuns.mktac3
                                (Prims.parse_int "0") "norm_term_env"
                                FStar_Tactics_Basic.norm_term_env
                                FStar_Reflection_Embeddings.e_env uu____312
                                FStar_Reflection_Embeddings.e_term
                                FStar_Reflection_Embeddings.e_term
                               in
                            let uu____319 =
                              let uu____322 =
                                let uu____323 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Syntax_Embeddings.e_norm_step
                                   in
                                FStar_Tactics_InterpFuns.mktac2
                                  (Prims.parse_int "0") "norm_binder_type"
                                  FStar_Tactics_Basic.norm_binder_type
                                  uu____323
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                 in
                              let uu____330 =
                                let uu____333 =
                                  FStar_Tactics_InterpFuns.mktac2
                                    (Prims.parse_int "0") "rename_to"
                                    FStar_Tactics_Basic.rename_to
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_string
                                    FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____334 =
                                  let uu____337 =
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "binder_retype"
                                      FStar_Tactics_Basic.binder_retype
                                      FStar_Reflection_Embeddings.e_binder
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____338 =
                                    let uu____341 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "revert"
                                        FStar_Tactics_Basic.revert
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____342 =
                                      let uu____345 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          (Prims.parse_int "0") "clear_top"
                                          FStar_Tactics_Basic.clear_top
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____346 =
                                        let uu____349 =
                                          FStar_Tactics_InterpFuns.mktac1
                                            (Prims.parse_int "0") "clear"
                                            FStar_Tactics_Basic.clear
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        let uu____350 =
                                          let uu____353 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "rewrite"
                                              FStar_Tactics_Basic.rewrite
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Syntax_Embeddings.e_unit
                                             in
                                          let uu____354 =
                                            let uu____357 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0") "smt"
                                                FStar_Tactics_Basic.smt
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Syntax_Embeddings.e_unit
                                               in
                                            let uu____358 =
                                              let uu____361 =
                                                FStar_Tactics_InterpFuns.mktac1
                                                  (Prims.parse_int "0")
                                                  "refine_intro"
                                                  FStar_Tactics_Basic.refine_intro
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Syntax_Embeddings.e_unit
                                                 in
                                              let uu____362 =
                                                let uu____365 =
                                                  FStar_Tactics_InterpFuns.mktac2
                                                    (Prims.parse_int "0")
                                                    "t_exact"
                                                    FStar_Tactics_Basic.t_exact
                                                    FStar_Syntax_Embeddings.e_bool
                                                    FStar_Reflection_Embeddings.e_term
                                                    FStar_Syntax_Embeddings.e_unit
                                                   in
                                                let uu____366 =
                                                  let uu____369 =
                                                    FStar_Tactics_InterpFuns.mktac1
                                                      (Prims.parse_int "0")
                                                      "apply"
                                                      (FStar_Tactics_Basic.apply
                                                         true)
                                                      FStar_Reflection_Embeddings.e_term
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____370 =
                                                    let uu____373 =
                                                      FStar_Tactics_InterpFuns.mktac1
                                                        (Prims.parse_int "0")
                                                        "apply_raw"
                                                        (FStar_Tactics_Basic.apply
                                                           false)
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Syntax_Embeddings.e_unit
                                                       in
                                                    let uu____374 =
                                                      let uu____377 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          (Prims.parse_int "0")
                                                          "apply_lemma"
                                                          FStar_Tactics_Basic.apply_lemma
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                         in
                                                      let uu____378 =
                                                        let uu____381 =
                                                          let uu____382 =
                                                            e_tactic_0'
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____387 =
                                                            e_tactic_0'
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          let uu____392 =
                                                            FStar_Syntax_Embeddings.e_tuple2
                                                              FStar_Syntax_Embeddings.e_any
                                                              FStar_Syntax_Embeddings.e_any
                                                             in
                                                          FStar_Tactics_InterpFuns.mktac5
                                                            (Prims.parse_int "2")
                                                            "__divide"
                                                            (fun uu____409 
                                                               ->
                                                               fun uu____410 
                                                                 ->
                                                                 FStar_Tactics_Basic.divide)
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Syntax_Embeddings.e_int
                                                            uu____382
                                                            uu____387
                                                            uu____392
                                                           in
                                                        let uu____411 =
                                                          let uu____414 =
                                                            let uu____415 =
                                                              e_tactic_0'
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____420 =
                                                              e_tactic_0'
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            FStar_Tactics_InterpFuns.mktac2
                                                              (Prims.parse_int "0")
                                                              "__seq"
                                                              FStar_Tactics_Basic.seq
                                                              uu____415
                                                              uu____420
                                                              FStar_Syntax_Embeddings.e_unit
                                                             in
                                                          let uu____429 =
                                                            let uu____432 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                (Prims.parse_int "0")
                                                                "set_options"
                                                                FStar_Tactics_Basic.set_options
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____433 =
                                                              let uu____436 =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  (Prims.parse_int "0")
                                                                  "tc"
                                                                  FStar_Tactics_Basic.tc
                                                                  FStar_Reflection_Embeddings.e_term
                                                                  FStar_Reflection_Embeddings.e_term
                                                                 in
                                                              let uu____437 =
                                                                let uu____440
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                   in
                                                                let uu____441
                                                                  =
                                                                  let uu____444
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                  let uu____445
                                                                    =
                                                                    let uu____448
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____449
                                                                    =
                                                                    let uu____452
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____453
                                                                    =
                                                                    let uu____456
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____457
                                                                    =
                                                                    let uu____460
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____461
                                                                    =
                                                                    let uu____464
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____465
                                                                    =
                                                                    let uu____468
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____469
                                                                    =
                                                                    let uu____472
                                                                    =
                                                                    let uu____473
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____473
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____480
                                                                    =
                                                                    let uu____483
                                                                    =
                                                                    let uu____484
                                                                    =
                                                                    let uu____496
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____496
                                                                     in
                                                                    let uu____507
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____484
                                                                    uu____507
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____523
                                                                    =
                                                                    let uu____526
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____527
                                                                    =
                                                                    let uu____530
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____531
                                                                    =
                                                                    let uu____534
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____535
                                                                    =
                                                                    let uu____538
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____539
                                                                    =
                                                                    let uu____542
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____543
                                                                    =
                                                                    let uu____546
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____547
                                                                    =
                                                                    let uu____550
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____551
                                                                    =
                                                                    let uu____554
                                                                    =
                                                                    let uu____555
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____555
                                                                     in
                                                                    let uu____566
                                                                    =
                                                                    let uu____569
                                                                    =
                                                                    let uu____570
                                                                    =
                                                                    let uu____579
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____579
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____570
                                                                     in
                                                                    let uu____596
                                                                    =
                                                                    let uu____599
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____600
                                                                    =
                                                                    let uu____603
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____604
                                                                    =
                                                                    let uu____607
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____608
                                                                    =
                                                                    let uu____611
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____612
                                                                    =
                                                                    let uu____615
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                     in
                                                                    let uu____616
                                                                    =
                                                                    let uu____619
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____620
                                                                    =
                                                                    let uu____623
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____624
                                                                    =
                                                                    let uu____627
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____628
                                                                    =
                                                                    let uu____631
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____632
                                                                    =
                                                                    let uu____635
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____636
                                                                    =
                                                                    let uu____639
                                                                    =
                                                                    let uu____640
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____640
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____647
                                                                    =
                                                                    let uu____650
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____651
                                                                    =
                                                                    let uu____654
                                                                    =
                                                                    let uu____655
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____655
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____662
                                                                    =
                                                                    let uu____665
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                     in
                                                                    let uu____666
                                                                    =
                                                                    let uu____669
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____670
                                                                    =
                                                                    let uu____673
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                     in
                                                                    let uu____674
                                                                    =
                                                                    let uu____677
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____678
                                                                    =
                                                                    let uu____681
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    [uu____681]
                                                                     in
                                                                    uu____677
                                                                    ::
                                                                    uu____678
                                                                     in
                                                                    uu____673
                                                                    ::
                                                                    uu____674
                                                                     in
                                                                    uu____669
                                                                    ::
                                                                    uu____670
                                                                     in
                                                                    uu____665
                                                                    ::
                                                                    uu____666
                                                                     in
                                                                    uu____654
                                                                    ::
                                                                    uu____662
                                                                     in
                                                                    uu____650
                                                                    ::
                                                                    uu____651
                                                                     in
                                                                    uu____639
                                                                    ::
                                                                    uu____647
                                                                     in
                                                                    uu____635
                                                                    ::
                                                                    uu____636
                                                                     in
                                                                    uu____631
                                                                    ::
                                                                    uu____632
                                                                     in
                                                                    uu____627
                                                                    ::
                                                                    uu____628
                                                                     in
                                                                    uu____623
                                                                    ::
                                                                    uu____624
                                                                     in
                                                                    uu____619
                                                                    ::
                                                                    uu____620
                                                                     in
                                                                    uu____615
                                                                    ::
                                                                    uu____616
                                                                     in
                                                                    uu____611
                                                                    ::
                                                                    uu____612
                                                                     in
                                                                    uu____607
                                                                    ::
                                                                    uu____608
                                                                     in
                                                                    uu____603
                                                                    ::
                                                                    uu____604
                                                                     in
                                                                    uu____599
                                                                    ::
                                                                    uu____600
                                                                     in
                                                                    uu____569
                                                                    ::
                                                                    uu____596
                                                                     in
                                                                    uu____554
                                                                    ::
                                                                    uu____566
                                                                     in
                                                                    uu____550
                                                                    ::
                                                                    uu____551
                                                                     in
                                                                    uu____546
                                                                    ::
                                                                    uu____547
                                                                     in
                                                                    uu____542
                                                                    ::
                                                                    uu____543
                                                                     in
                                                                    uu____538
                                                                    ::
                                                                    uu____539
                                                                     in
                                                                    uu____534
                                                                    ::
                                                                    uu____535
                                                                     in
                                                                    uu____530
                                                                    ::
                                                                    uu____531
                                                                     in
                                                                    uu____526
                                                                    ::
                                                                    uu____527
                                                                     in
                                                                    uu____483
                                                                    ::
                                                                    uu____523
                                                                     in
                                                                    uu____472
                                                                    ::
                                                                    uu____480
                                                                     in
                                                                    uu____468
                                                                    ::
                                                                    uu____469
                                                                     in
                                                                    uu____464
                                                                    ::
                                                                    uu____465
                                                                     in
                                                                    uu____460
                                                                    ::
                                                                    uu____461
                                                                     in
                                                                    uu____456
                                                                    ::
                                                                    uu____457
                                                                     in
                                                                    uu____452
                                                                    ::
                                                                    uu____453
                                                                     in
                                                                    uu____448
                                                                    ::
                                                                    uu____449
                                                                     in
                                                                  uu____444
                                                                    ::
                                                                    uu____445
                                                                   in
                                                                uu____440 ::
                                                                  uu____441
                                                                 in
                                                              uu____436 ::
                                                                uu____437
                                                               in
                                                            uu____432 ::
                                                              uu____433
                                                             in
                                                          uu____414 ::
                                                            uu____429
                                                           in
                                                        uu____381 ::
                                                          uu____411
                                                         in
                                                      uu____377 :: uu____378
                                                       in
                                                    uu____373 :: uu____374
                                                     in
                                                  uu____369 :: uu____370  in
                                                uu____365 :: uu____366  in
                                              uu____361 :: uu____362  in
                                            uu____357 :: uu____358  in
                                          uu____353 :: uu____354  in
                                        uu____349 :: uu____350  in
                                      uu____345 :: uu____346  in
                                    uu____341 :: uu____342  in
                                  uu____337 :: uu____338  in
                                uu____333 :: uu____334  in
                              uu____322 :: uu____330  in
                            uu____311 :: uu____319  in
                          uu____300 :: uu____308  in
                        uu____285 :: uu____297  in
                      uu____281 :: uu____282  in
                    uu____261 :: uu____278  in
                  uu____257 :: uu____258  in
                uu____251 :: uu____254  in
              uu____219 :: uu____248  in
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
               let uu____704 =
                 let uu____709 =
                   let uu____710 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____710]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____709  in
               uu____704 FStar_Pervasives_Native.None rng  in
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
             let uu____758 =
               let uu____763 =
                 let uu____764 =
                   let uu____773 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____773  in
                 [uu____764]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____763  in
             uu____758 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Env.Weak;
             FStar_TypeChecker_Env.Reify;
             FStar_TypeChecker_Env.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Env.UnfoldTac;
             FStar_TypeChecker_Env.Primops;
             FStar_TypeChecker_Env.Unascribe]  in
           let norm_f =
             let uu____816 = FStar_Options.tactics_nbe ()  in
             if uu____816
             then FStar_TypeChecker_NBE.normalize_with_primitive_steps
             else FStar_TypeChecker_Normalize.normalize_with_primitive_steps
              in
           if proof_state.FStar_Tactics_Types.tac_verb_dbg
           then
             (let uu____835 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____835)
           else ();
           (let result =
              let uu____838 = primitive_steps ()  in
              norm_f uu____838 steps
                proof_state.FStar_Tactics_Types.main_context tm
               in
            if proof_state.FStar_Tactics_Types.tac_verb_dbg
            then
              (let uu____842 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____842)
            else ();
            (let res =
               let uu____849 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____849 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____862 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____862
                   (fun uu____866  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____871 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____871
                   (fun uu____875  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____878 =
                   let uu____883 =
                     let uu____884 = FStar_Syntax_Print.term_to_string result
                        in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____884
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____883)  in
                 FStar_Errors.raise_error uu____878
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____891 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
        uu____891

let report_implicits :
  'Auu____908 . 'Auu____908 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____937 =
               let uu____938 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____939 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____938 uu____939 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____937, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____978 = FStar_ST.op_Bang tacdbg  in
             if uu____978
             then
               let uu____998 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____998
             else ());
            (let uu____1000 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1000 with
             | (uu____1013,uu____1014,g) ->
                 ((let uu____1017 = FStar_ST.op_Bang tacdbg  in
                   if uu____1017 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                      in
                   let uu____1043 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1043 with
                   | (env1,uu____1057) ->
                       let env2 =
                         let uu___349_1063 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___349_1063.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___349_1063.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___349_1063.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___349_1063.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___349_1063.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___349_1063.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___349_1063.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___349_1063.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___349_1063.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___349_1063.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___349_1063.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___349_1063.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___349_1063.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___349_1063.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___349_1063.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___349_1063.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___349_1063.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___349_1063.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___349_1063.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___349_1063.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___349_1063.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___349_1063.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___349_1063.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___349_1063.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___349_1063.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___349_1063.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___349_1063.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___349_1063.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___349_1063.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___349_1063.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___349_1063.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___349_1063.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___349_1063.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___349_1063.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___349_1063.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___349_1063.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___349_1063.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___349_1063.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___349_1063.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___349_1063.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___349_1063.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___350_1065 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___350_1065.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___350_1065.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___350_1065.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___350_1065.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___350_1065.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___350_1065.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___350_1065.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___350_1065.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___350_1065.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___350_1065.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___350_1065.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___350_1065.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___350_1065.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___350_1065.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___350_1065.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___350_1065.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___350_1065.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___350_1065.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___350_1065.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___350_1065.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___350_1065.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___350_1065.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___350_1065.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___350_1065.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___350_1065.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___350_1065.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___350_1065.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___350_1065.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___350_1065.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___350_1065.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___350_1065.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___350_1065.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___350_1065.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___350_1065.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___350_1065.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___350_1065.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___350_1065.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___350_1065.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___350_1065.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___350_1065.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___350_1065.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___351_1067 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___351_1067.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___351_1067.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___351_1067.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___351_1067.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___351_1067.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___351_1067.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___351_1067.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___351_1067.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___351_1067.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___351_1067.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___351_1067.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___351_1067.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___351_1067.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___351_1067.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___351_1067.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___351_1067.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___351_1067.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___351_1067.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___351_1067.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___351_1067.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___351_1067.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___351_1067.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___351_1067.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___351_1067.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___351_1067.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___351_1067.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___351_1067.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___351_1067.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___351_1067.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___351_1067.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___351_1067.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___351_1067.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___351_1067.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___351_1067.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___351_1067.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___351_1067.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___351_1067.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___351_1067.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___351_1067.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___351_1067.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___351_1067.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____1069 = FStar_Range.use_range rng_goal  in
                         let uu____1070 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1069 uu____1070  in
                       let uu____1071 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1071 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1109 = FStar_ST.op_Bang tacdbg  in
                              if uu____1109
                              then
                                let uu____1129 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____1129
                              else ());
                             (let uu____1131 =
                                FStar_Util.record_time
                                  (fun uu____1141  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____1131 with
                              | (res,ms) ->
                                  ((let uu____1155 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____1155
                                    then
                                      let uu____1175 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____1176 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____1177 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____1175 uu____1176 uu____1177
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____1185,ps1) ->
                                        ((let uu____1188 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1188
                                          then
                                            let uu____1208 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____1208
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____1215 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____1215
                                              then
                                                let uu____1216 =
                                                  let uu____1217 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____1218 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____1217 uu____1218
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____1216
                                                 then ()
                                                 else
                                                   (let uu____1220 =
                                                      let uu____1221 =
                                                        let uu____1222 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____1222
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____1221
                                                       in
                                                    failwith uu____1220))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____1225 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1225
                                          then
                                            let uu____1245 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____1245
                                          else ());
                                         (let g1 =
                                            let uu___352_1250 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___352_1250.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___352_1250.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___352_1250.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____1253 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____1253
                                           then
                                             let uu____1273 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print1
                                               "Checked (1) implicits: %s\n"
                                               uu____1273
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____1279 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1279
                                            then
                                              let uu____1299 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "Checked (2) implicits: %s\n"
                                                uu____1299
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____1309 =
                                            let uu____1310 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____1310 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____1309
                                            "at the time of failure");
                                         (let uu____1311 =
                                            let uu____1316 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____1316)
                                             in
                                          FStar_Errors.raise_error uu____1311
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____1328 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____1334 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____1340 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____1395 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____1435 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____1489 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____1530 . 'Auu____1530 -> 'Auu____1530 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1558 = FStar_Syntax_Util.head_and_args t  in
        match uu____1558 with
        | (hd1,args) ->
            let uu____1601 =
              let uu____1616 =
                let uu____1617 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1617.FStar_Syntax_Syntax.n  in
              (uu____1616, args)  in
            (match uu____1601 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1632))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____1695 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1695 with
                       | (gs,uu____1703) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____1710 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1710 with
                       | (gs,uu____1718) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____1761 =
                        let uu____1768 =
                          let uu____1771 =
                            let uu____1772 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____1772
                             in
                          [uu____1771]  in
                        (FStar_Syntax_Util.t_true, uu____1768)  in
                      Simplified uu____1761
                  | Both  ->
                      let uu____1783 =
                        let uu____1792 =
                          let uu____1795 =
                            let uu____1796 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____1796
                             in
                          [uu____1795]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____1792)  in
                      Dual uu____1783
                  | Neg  -> Simplified (assertion, []))
             | uu____1809 -> Unchanged t)
  
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
    fun uu___344_1899  ->
      match uu___344_1899 with
      | Unchanged t -> let uu____1905 = f t  in Unchanged uu____1905
      | Simplified (t,gs) ->
          let uu____1912 = let uu____1919 = f t  in (uu____1919, gs)  in
          Simplified uu____1912
      | Dual (tn,tp,gs) ->
          let uu____1929 =
            let uu____1938 = f tn  in
            let uu____1939 = f tp  in (uu____1938, uu____1939, gs)  in
          Dual uu____1929
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2002 = f t1 t2  in Unchanged uu____2002
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2014 = let uu____2021 = f t1 t2  in (uu____2021, gs)
               in
            Simplified uu____2014
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2035 = let uu____2042 = f t1 t2  in (uu____2042, gs)
               in
            Simplified uu____2035
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2061 =
              let uu____2068 = f t1 t2  in
              (uu____2068, (FStar_List.append gs1 gs2))  in
            Simplified uu____2061
        | uu____2071 ->
            let uu____2080 = explode x  in
            (match uu____2080 with
             | (n1,p1,gs1) ->
                 let uu____2098 = explode y  in
                 (match uu____2098 with
                  | (n2,p2,gs2) ->
                      let uu____2116 =
                        let uu____2125 = f n1 n2  in
                        let uu____2126 = f p1 p2  in
                        (uu____2125, uu____2126, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____2116))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____2198 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____2198
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____2246  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____2288 =
              let uu____2289 = FStar_Syntax_Subst.compress t  in
              uu____2289.FStar_Syntax_Syntax.n  in
            match uu____2288 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____2301 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____2301 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____2327 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____2327 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2347;
                   FStar_Syntax_Syntax.vars = uu____2348;_},(p,uu____2350)::
                 (q,uu____2352)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2408 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2408
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____2411 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____2411 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____2425 = FStar_Syntax_Util.mk_imp l r  in
                       uu____2425.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2429;
                   FStar_Syntax_Syntax.vars = uu____2430;_},(p,uu____2432)::
                 (q,uu____2434)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____2490 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2490
                   in
                let xq =
                  let uu____2492 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2492
                   in
                let r1 =
                  let uu____2494 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____2494 p  in
                let r2 =
                  let uu____2496 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____2496 q  in
                (match (r1, r2) with
                 | (Unchanged uu____2503,Unchanged uu____2504) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____2522 = FStar_Syntax_Util.mk_iff l r  in
                            uu____2522.FStar_Syntax_Syntax.n) r1 r2
                 | uu____2525 ->
                     let uu____2534 = explode r1  in
                     (match uu____2534 with
                      | (pn,pp,gs1) ->
                          let uu____2552 = explode r2  in
                          (match uu____2552 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____2573 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____2576 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____2573
                                   uu____2576
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____2640  ->
                       fun r  ->
                         match uu____2640 with
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
                let uu____2792 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____2792 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____2832  ->
                            match uu____2832 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____2854 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___353_2886 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___353_2886.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___353_2886.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____2854 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____2914 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____2914.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____2960 = traverse f pol e t1  in
                let uu____2965 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____2965 uu____2960
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___354_3005 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___354_3005.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___354_3005.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3012 =
                f pol e
                  (let uu___355_3016 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___355_3016.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___355_3016.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3012
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___356_3026 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___356_3026.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___356_3026.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3027 = explode rp  in
              (match uu____3027 with
               | (uu____3036,p',gs') ->
                   Dual
                     ((let uu___357_3046 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___357_3046.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___357_3046.FStar_Syntax_Syntax.vars)
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
      (let uu____3089 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____3089);
      (let uu____3110 = FStar_ST.op_Bang tacdbg  in
       if uu____3110
       then
         let uu____3130 =
           let uu____3131 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____3131
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____3132 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3130
           uu____3132
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____3161 =
         let uu____3170 = traverse by_tactic_interp Pos env goal  in
         match uu____3170 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____3194 -> failwith "no"  in
       match uu____3161 with
       | (t',gs) ->
           ((let uu____3222 = FStar_ST.op_Bang tacdbg  in
             if uu____3222
             then
               let uu____3242 =
                 let uu____3243 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____3243
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____3244 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3242 uu____3244
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3292  ->
                    fun g  ->
                      match uu____3292 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3337 =
                              let uu____3340 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____3341 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____3340 uu____3341  in
                            match uu____3337 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3342 =
                                  let uu____3347 =
                                    let uu____3348 =
                                      let uu____3349 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____3349
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____3348
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____3347)
                                   in
                                FStar_Errors.raise_error uu____3342
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____3352 = FStar_ST.op_Bang tacdbg  in
                            if uu____3352
                            then
                              let uu____3372 = FStar_Util.string_of_int n1
                                 in
                              let uu____3373 =
                                let uu____3374 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____3374
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3372 uu____3373
                            else ());
                           (let gt' =
                              let uu____3377 =
                                let uu____3378 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____3378
                                 in
                              FStar_TypeChecker_Util.label uu____3377
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____3379 =
                              let uu____3388 =
                                let uu____3395 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____3395, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____3388 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____3379)))) s
                 gs
                in
             let uu____3410 = s1  in
             match uu____3410 with
             | (uu____3431,gs1) ->
                 let uu____3449 =
                   let uu____3456 = FStar_Options.peek ()  in
                   (env, t', uu____3456)  in
                 uu____3449 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____3469 =
        let uu____3470 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____3470  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3469 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____3471 =
      let uu____3476 =
        let uu____3477 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____3486 =
          let uu____3497 = FStar_Syntax_Syntax.as_arg a  in [uu____3497]  in
        uu____3477 :: uu____3486  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3476  in
    uu____3471 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____3547 =
            let uu____3552 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____3553 =
              let uu____3554 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3554]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____3552 uu____3553  in
          uu____3547 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____3583 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____3583);
           (let uu____3603 =
              let uu____3610 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____3610 env typ
               in
            match uu____3603 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____3624 =
                        let uu____3627 = FStar_Tactics_Types.goal_env g  in
                        let uu____3628 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____3627 uu____3628  in
                      match uu____3624 with
                      | FStar_Pervasives_Native.Some vc ->
                          let guard =
                            {
                              FStar_TypeChecker_Env.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Env.deferred = [];
                              FStar_TypeChecker_Env.univ_ineqs = ([], []);
                              FStar_TypeChecker_Env.implicits = []
                            }  in
                          let uu____3639 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____3639 guard
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
        ((let uu____3656 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____3656);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____3677 =
            let uu____3684 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____3684 env typ
             in
          match uu____3677 with
          | (gs,w) ->
              ((let uu____3694 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____3698 =
                         let uu____3699 =
                           let uu____3702 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____3703 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____3702 uu____3703  in
                         FStar_Option.isSome uu____3699  in
                       Prims.op_Negation uu____3698) gs
                   in
                if uu____3694
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
                (let uu____3707 = FStar_ST.op_Bang tacdbg  in
                 if uu____3707
                 then
                   let uu____3727 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____3727
                 else ());
                (let uu____3729 =
                   let uu____3734 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Syntax_Embeddings.unembed uu____3734 w1  in
                 match uu____3729 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  