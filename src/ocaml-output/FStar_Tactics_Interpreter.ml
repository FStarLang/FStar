open Prims
let (tacdbg : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let mktot1' :
  'Auu____38 'Auu____39 'Auu____40 'Auu____41 .
    Prims.int ->
      Prims.string ->
        ('Auu____38 -> 'Auu____39) ->
          'Auu____38 FStar_Syntax_Embeddings.embedding ->
            'Auu____39 FStar_Syntax_Embeddings.embedding ->
              ('Auu____40 -> 'Auu____41) ->
                'Auu____40 FStar_TypeChecker_NBETerm.embedding ->
                  'Auu____41 FStar_TypeChecker_NBETerm.embedding ->
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
                  let uu___351_108 =
                    FStar_Tactics_InterpFuns.mktot1 uarity nm f ea er nf ena
                      enr
                     in
                  let uu____109 =
                    FStar_Ident.lid_of_str
                      (Prims.strcat "FStar.Tactics.Types." nm)
                     in
                  {
                    FStar_TypeChecker_Cfg.name = uu____109;
                    FStar_TypeChecker_Cfg.arity =
                      (uu___351_108.FStar_TypeChecker_Cfg.arity);
                    FStar_TypeChecker_Cfg.univ_arity =
                      (uu___351_108.FStar_TypeChecker_Cfg.univ_arity);
                    FStar_TypeChecker_Cfg.auto_reflect =
                      (uu___351_108.FStar_TypeChecker_Cfg.auto_reflect);
                    FStar_TypeChecker_Cfg.strong_reduction_ok =
                      (uu___351_108.FStar_TypeChecker_Cfg.strong_reduction_ok);
                    FStar_TypeChecker_Cfg.requires_binder_substitution =
                      (uu___351_108.FStar_TypeChecker_Cfg.requires_binder_substitution);
                    FStar_TypeChecker_Cfg.interpretation =
                      (uu___351_108.FStar_TypeChecker_Cfg.interpretation);
                    FStar_TypeChecker_Cfg.interpretation_nbe =
                      (uu___351_108.FStar_TypeChecker_Cfg.interpretation_nbe)
                  }
  
let mktot2' :
  'Auu____142 'Auu____143 'Auu____144 'Auu____145 'Auu____146 'Auu____147 .
    Prims.int ->
      Prims.string ->
        ('Auu____142 -> 'Auu____143 -> 'Auu____144) ->
          'Auu____142 FStar_Syntax_Embeddings.embedding ->
            'Auu____143 FStar_Syntax_Embeddings.embedding ->
              'Auu____144 FStar_Syntax_Embeddings.embedding ->
                ('Auu____145 -> 'Auu____146 -> 'Auu____147) ->
                  'Auu____145 FStar_TypeChecker_NBETerm.embedding ->
                    'Auu____146 FStar_TypeChecker_NBETerm.embedding ->
                      'Auu____147 FStar_TypeChecker_NBETerm.embedding ->
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
                      let uu___352_242 =
                        FStar_Tactics_InterpFuns.mktot2 uarity nm f ea eb er
                          nf ena enb enr
                         in
                      let uu____243 =
                        FStar_Ident.lid_of_str
                          (Prims.strcat "FStar.Tactics.Types." nm)
                         in
                      {
                        FStar_TypeChecker_Cfg.name = uu____243;
                        FStar_TypeChecker_Cfg.arity =
                          (uu___352_242.FStar_TypeChecker_Cfg.arity);
                        FStar_TypeChecker_Cfg.univ_arity =
                          (uu___352_242.FStar_TypeChecker_Cfg.univ_arity);
                        FStar_TypeChecker_Cfg.auto_reflect =
                          (uu___352_242.FStar_TypeChecker_Cfg.auto_reflect);
                        FStar_TypeChecker_Cfg.strong_reduction_ok =
                          (uu___352_242.FStar_TypeChecker_Cfg.strong_reduction_ok);
                        FStar_TypeChecker_Cfg.requires_binder_substitution =
                          (uu___352_242.FStar_TypeChecker_Cfg.requires_binder_substitution);
                        FStar_TypeChecker_Cfg.interpretation =
                          (uu___352_242.FStar_TypeChecker_Cfg.interpretation);
                        FStar_TypeChecker_Cfg.interpretation_nbe =
                          (uu___352_242.FStar_TypeChecker_Cfg.interpretation_nbe)
                      }
  
let rec e_tactic_0 :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____485 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____492  ->
         fun uu____493  ->
           fun uu____494  ->
             fun uu____495  -> failwith "Impossible: embedding tactic (0)?")
      (fun t  ->
         fun w  ->
           fun norm1  ->
             let uu____528 = unembed_tactic_0 er t norm1  in
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16) uu____528)
      uu____485

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____547 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____557  ->
           fun uu____558  ->
             fun uu____559  ->
               fun uu____560  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  -> fun w  -> unembed_tactic_1 ea er t) uu____547

and e_tactic_nbe_0 :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____593 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____599  -> failwith "Impossible: NBE embedding tactic (0)?")
      (fun cb  ->
         fun t  ->
           let uu____615 = unembed_tactic_nbe_0 er cb t  in
           FStar_All.pipe_left
             (fun _0_17  -> FStar_Pervasives_Native.Some _0_17) uu____615)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____593

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____636 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____645  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  -> fun t  -> unembed_tactic_nbe_1 ea er cb t)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____636

and (primitive_steps :
  unit -> FStar_TypeChecker_Cfg.primitive_step Prims.list) =
  fun uu____666  ->
    let uu____669 =
      let uu____672 =
        mktot1' (Prims.parse_int "0") "tracepoint"
          FStar_Tactics_Types.tracepoint FStar_Tactics_Embedding.e_proofstate
          FStar_Syntax_Embeddings.e_unit FStar_Tactics_Types.tracepoint
          FStar_Tactics_Embedding.e_proofstate_nbe
          FStar_TypeChecker_NBETerm.e_unit
         in
      let uu____673 =
        let uu____676 =
          mktot2' (Prims.parse_int "0") "set_proofstate_range"
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Syntax_Embeddings.e_range
            FStar_Tactics_Embedding.e_proofstate
            FStar_Tactics_Types.set_proofstate_range
            FStar_Tactics_Embedding.e_proofstate_nbe
            FStar_TypeChecker_NBETerm.e_range
            FStar_Tactics_Embedding.e_proofstate_nbe
           in
        let uu____677 =
          let uu____680 =
            mktot1' (Prims.parse_int "0") "incr_depth"
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Embedding.e_proofstate
              FStar_Tactics_Types.incr_depth
              FStar_Tactics_Embedding.e_proofstate_nbe
              FStar_Tactics_Embedding.e_proofstate_nbe
             in
          let uu____681 =
            let uu____684 =
              mktot1' (Prims.parse_int "0") "decr_depth"
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Embedding.e_proofstate
                FStar_Tactics_Types.decr_depth
                FStar_Tactics_Embedding.e_proofstate_nbe
                FStar_Tactics_Embedding.e_proofstate_nbe
               in
            let uu____685 =
              let uu____688 =
                let uu____689 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Tactics_Embedding.e_goal
                   in
                let uu____694 =
                  FStar_TypeChecker_NBETerm.e_list
                    FStar_Tactics_Embedding.e_goal_nbe
                   in
                mktot1' (Prims.parse_int "0") "goals"
                  FStar_Tactics_Types.goals
                  FStar_Tactics_Embedding.e_proofstate uu____689
                  FStar_Tactics_Types.goals
                  FStar_Tactics_Embedding.e_proofstate_nbe uu____694
                 in
              let uu____703 =
                let uu____706 =
                  let uu____707 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Tactics_Embedding.e_goal
                     in
                  let uu____712 =
                    FStar_TypeChecker_NBETerm.e_list
                      FStar_Tactics_Embedding.e_goal_nbe
                     in
                  mktot1' (Prims.parse_int "0") "smtgoals"
                    FStar_Tactics_Types.smtgoals
                    FStar_Tactics_Embedding.e_proofstate uu____707
                    FStar_Tactics_Types.smtgoals
                    FStar_Tactics_Embedding.e_proofstate_nbe uu____712
                   in
                let uu____721 =
                  let uu____724 =
                    mktot1' (Prims.parse_int "0") "goal_env"
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal
                      FStar_Reflection_Embeddings.e_env
                      FStar_Tactics_Types.goal_env
                      FStar_Tactics_Embedding.e_goal_nbe
                      FStar_Reflection_NBEEmbeddings.e_env
                     in
                  let uu____725 =
                    let uu____728 =
                      mktot1' (Prims.parse_int "0") "goal_type"
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal
                        FStar_Reflection_Embeddings.e_term
                        FStar_Tactics_Types.goal_type
                        FStar_Tactics_Embedding.e_goal_nbe
                        FStar_Reflection_NBEEmbeddings.e_term
                       in
                    let uu____729 =
                      let uu____732 =
                        mktot1' (Prims.parse_int "0") "goal_witness"
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal
                          FStar_Reflection_Embeddings.e_term
                          FStar_Tactics_Types.goal_witness
                          FStar_Tactics_Embedding.e_goal_nbe
                          FStar_Reflection_NBEEmbeddings.e_term
                         in
                      let uu____733 =
                        let uu____736 =
                          FStar_Tactics_InterpFuns.mktot2
                            (Prims.parse_int "0") "push_binder"
                            (fun env  ->
                               fun b  ->
                                 FStar_TypeChecker_Env.push_binders env [b])
                            FStar_Reflection_Embeddings.e_env
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Reflection_Embeddings.e_env
                            (fun env  ->
                               fun b  ->
                                 FStar_TypeChecker_Env.push_binders env [b])
                            FStar_Reflection_NBEEmbeddings.e_env
                            FStar_Reflection_NBEEmbeddings.e_binder
                            FStar_Reflection_NBEEmbeddings.e_env
                           in
                        let uu____793 =
                          let uu____796 =
                            FStar_Tactics_InterpFuns.mktac2
                              (Prims.parse_int "1") "fail"
                              (fun uu____798  -> FStar_Tactics_Basic.fail)
                              FStar_Syntax_Embeddings.e_any
                              FStar_Syntax_Embeddings.e_string
                              FStar_Syntax_Embeddings.e_any
                              (fun uu____800  -> FStar_Tactics_Basic.fail)
                              FStar_TypeChecker_NBETerm.e_any
                              FStar_TypeChecker_NBETerm.e_string
                              FStar_TypeChecker_NBETerm.e_any
                             in
                          let uu____801 =
                            let uu____804 =
                              FStar_Tactics_InterpFuns.mktac1
                                (Prims.parse_int "0") "trivial"
                                FStar_Tactics_Basic.trivial
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Tactics_Basic.trivial
                                FStar_TypeChecker_NBETerm.e_unit
                                FStar_TypeChecker_NBETerm.e_unit
                               in
                            let uu____805 =
                              let uu____808 =
                                let uu____809 =
                                  e_tactic_0 FStar_Syntax_Embeddings.e_any
                                   in
                                let uu____814 =
                                  FStar_Syntax_Embeddings.e_either
                                    FStar_Syntax_Embeddings.e_string
                                    FStar_Syntax_Embeddings.e_any
                                   in
                                let uu____821 =
                                  e_tactic_nbe_0
                                    FStar_TypeChecker_NBETerm.e_any
                                   in
                                let uu____826 =
                                  FStar_TypeChecker_NBETerm.e_either
                                    FStar_TypeChecker_NBETerm.e_string
                                    FStar_TypeChecker_NBETerm.e_any
                                   in
                                FStar_Tactics_InterpFuns.mktac2
                                  (Prims.parse_int "1") "__catch"
                                  (fun uu____846  ->
                                     FStar_Tactics_Basic.catch)
                                  FStar_Syntax_Embeddings.e_any uu____809
                                  uu____814
                                  (fun uu____848  ->
                                     FStar_Tactics_Basic.catch)
                                  FStar_TypeChecker_NBETerm.e_any uu____821
                                  uu____826
                                 in
                              let uu____849 =
                                let uu____852 =
                                  FStar_Tactics_InterpFuns.mktac1
                                    (Prims.parse_int "0") "intro"
                                    FStar_Tactics_Basic.intro
                                    FStar_Syntax_Embeddings.e_unit
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Tactics_Basic.intro
                                    FStar_TypeChecker_NBETerm.e_unit
                                    FStar_Reflection_NBEEmbeddings.e_binder
                                   in
                                let uu____853 =
                                  let uu____856 =
                                    let uu____857 =
                                      FStar_Syntax_Embeddings.e_tuple2
                                        FStar_Reflection_Embeddings.e_binder
                                        FStar_Reflection_Embeddings.e_binder
                                       in
                                    let uu____864 =
                                      FStar_TypeChecker_NBETerm.e_tuple2
                                        FStar_Reflection_NBEEmbeddings.e_binder
                                        FStar_Reflection_NBEEmbeddings.e_binder
                                       in
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "intro_rec"
                                      FStar_Tactics_Basic.intro_rec
                                      FStar_Syntax_Embeddings.e_unit
                                      uu____857 FStar_Tactics_Basic.intro_rec
                                      FStar_TypeChecker_NBETerm.e_unit
                                      uu____864
                                     in
                                  let uu____879 =
                                    let uu____882 =
                                      let uu____883 =
                                        FStar_Syntax_Embeddings.e_list
                                          FStar_Syntax_Embeddings.e_norm_step
                                         in
                                      let uu____888 =
                                        FStar_TypeChecker_NBETerm.e_list
                                          FStar_TypeChecker_NBETerm.e_norm_step
                                         in
                                      FStar_Tactics_InterpFuns.mktac1
                                        (Prims.parse_int "0") "norm"
                                        FStar_Tactics_Basic.norm uu____883
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Tactics_Basic.norm uu____888
                                        FStar_TypeChecker_NBETerm.e_unit
                                       in
                                    let uu____897 =
                                      let uu____900 =
                                        let uu____901 =
                                          FStar_Syntax_Embeddings.e_list
                                            FStar_Syntax_Embeddings.e_norm_step
                                           in
                                        let uu____906 =
                                          FStar_TypeChecker_NBETerm.e_list
                                            FStar_TypeChecker_NBETerm.e_norm_step
                                           in
                                        FStar_Tactics_InterpFuns.mktac3
                                          (Prims.parse_int "0")
                                          "norm_term_env"
                                          FStar_Tactics_Basic.norm_term_env
                                          FStar_Reflection_Embeddings.e_env
                                          uu____901
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Tactics_Basic.norm_term_env
                                          FStar_Reflection_NBEEmbeddings.e_env
                                          uu____906
                                          FStar_Reflection_NBEEmbeddings.e_term
                                          FStar_Reflection_NBEEmbeddings.e_term
                                         in
                                      let uu____915 =
                                        let uu____918 =
                                          let uu____919 =
                                            FStar_Syntax_Embeddings.e_list
                                              FStar_Syntax_Embeddings.e_norm_step
                                             in
                                          let uu____924 =
                                            FStar_TypeChecker_NBETerm.e_list
                                              FStar_TypeChecker_NBETerm.e_norm_step
                                             in
                                          FStar_Tactics_InterpFuns.mktac2
                                            (Prims.parse_int "0")
                                            "norm_binder_type"
                                            FStar_Tactics_Basic.norm_binder_type
                                            uu____919
                                            FStar_Reflection_Embeddings.e_binder
                                            FStar_Syntax_Embeddings.e_unit
                                            FStar_Tactics_Basic.norm_binder_type
                                            uu____924
                                            FStar_Reflection_NBEEmbeddings.e_binder
                                            FStar_TypeChecker_NBETerm.e_unit
                                           in
                                        let uu____933 =
                                          let uu____936 =
                                            FStar_Tactics_InterpFuns.mktac2
                                              (Prims.parse_int "0")
                                              "rename_to"
                                              FStar_Tactics_Basic.rename_to
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Syntax_Embeddings.e_string
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Tactics_Basic.rename_to
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                              FStar_TypeChecker_NBETerm.e_string
                                              FStar_TypeChecker_NBETerm.e_unit
                                             in
                                          let uu____937 =
                                            let uu____940 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                (Prims.parse_int "0")
                                                "binder_retype"
                                                FStar_Tactics_Basic.binder_retype
                                                FStar_Reflection_Embeddings.e_binder
                                                FStar_Syntax_Embeddings.e_unit
                                                FStar_Tactics_Basic.binder_retype
                                                FStar_Reflection_NBEEmbeddings.e_binder
                                                FStar_TypeChecker_NBETerm.e_unit
                                               in
                                            let uu____941 =
                                              let uu____944 =
                                                FStar_Tactics_InterpFuns.mktac1
                                                  (Prims.parse_int "0")
                                                  "revert"
                                                  FStar_Tactics_Basic.revert
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.revert
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____945 =
                                                let uu____948 =
                                                  FStar_Tactics_InterpFuns.mktac1
                                                    (Prims.parse_int "0")
                                                    "clear_top"
                                                    FStar_Tactics_Basic.clear_top
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Syntax_Embeddings.e_unit
                                                    FStar_Tactics_Basic.clear_top
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                    FStar_TypeChecker_NBETerm.e_unit
                                                   in
                                                let uu____949 =
                                                  let uu____952 =
                                                    FStar_Tactics_InterpFuns.mktac1
                                                      (Prims.parse_int "0")
                                                      "clear"
                                                      FStar_Tactics_Basic.clear
                                                      FStar_Reflection_Embeddings.e_binder
                                                      FStar_Syntax_Embeddings.e_unit
                                                      FStar_Tactics_Basic.clear
                                                      FStar_Reflection_NBEEmbeddings.e_binder
                                                      FStar_TypeChecker_NBETerm.e_unit
                                                     in
                                                  let uu____953 =
                                                    let uu____956 =
                                                      FStar_Tactics_InterpFuns.mktac1
                                                        (Prims.parse_int "0")
                                                        "rewrite"
                                                        FStar_Tactics_Basic.rewrite
                                                        FStar_Reflection_Embeddings.e_binder
                                                        FStar_Syntax_Embeddings.e_unit
                                                        FStar_Tactics_Basic.rewrite
                                                        FStar_Reflection_NBEEmbeddings.e_binder
                                                        FStar_TypeChecker_NBETerm.e_unit
                                                       in
                                                    let uu____957 =
                                                      let uu____960 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          (Prims.parse_int "0")
                                                          "smt"
                                                          FStar_Tactics_Basic.smt
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Syntax_Embeddings.e_unit
                                                          FStar_Tactics_Basic.smt
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                          FStar_TypeChecker_NBETerm.e_unit
                                                         in
                                                      let uu____961 =
                                                        let uu____964 =
                                                          FStar_Tactics_InterpFuns.mktac1
                                                            (Prims.parse_int "0")
                                                            "refine_intro"
                                                            FStar_Tactics_Basic.refine_intro
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Syntax_Embeddings.e_unit
                                                            FStar_Tactics_Basic.refine_intro
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                            FStar_TypeChecker_NBETerm.e_unit
                                                           in
                                                        let uu____965 =
                                                          let uu____968 =
                                                            FStar_Tactics_InterpFuns.mktac3
                                                              (Prims.parse_int "0")
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
                                                          let uu____969 =
                                                            let uu____972 =
                                                              FStar_Tactics_InterpFuns.mktac2
                                                                (Prims.parse_int "1")
                                                                "t_apply"
                                                                FStar_Tactics_Basic.t_apply
                                                                FStar_Syntax_Embeddings.e_bool
                                                                FStar_Reflection_Embeddings.e_term
                                                                FStar_Syntax_Embeddings.e_unit
                                                                FStar_Tactics_Basic.t_apply
                                                                FStar_TypeChecker_NBETerm.e_bool
                                                                FStar_Reflection_NBEEmbeddings.e_term
                                                                FStar_TypeChecker_NBETerm.e_unit
                                                               in
                                                            let uu____973 =
                                                              let uu____976 =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  (Prims.parse_int "0")
                                                                  "apply_lemma"
                                                                  FStar_Tactics_Basic.apply_lemma
                                                                  FStar_Reflection_Embeddings.e_term
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                  FStar_Tactics_Basic.apply_lemma
                                                                  FStar_Reflection_NBEEmbeddings.e_term
                                                                  FStar_TypeChecker_NBETerm.e_unit
                                                                 in
                                                              let uu____977 =
                                                                let uu____980
                                                                  =
                                                                  let uu____981
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                  let uu____986
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                  let uu____991
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                  let uu____998
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                  let uu____1003
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                  let uu____1008
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                  FStar_Tactics_InterpFuns.mktac5
                                                                    (Prims.parse_int "2")
                                                                    "__divide"
                                                                    (
                                                                    fun
                                                                    uu____1033
                                                                     ->
                                                                    fun
                                                                    uu____1034
                                                                     ->
                                                                    FStar_Tactics_Basic.divide)
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    uu____981
                                                                    uu____986
                                                                    uu____991
                                                                    (
                                                                    fun
                                                                    uu____1037
                                                                     ->
                                                                    fun
                                                                    uu____1038
                                                                     ->
                                                                    FStar_Tactics_Basic.divide)
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    uu____998
                                                                    uu____1003
                                                                    uu____1008
                                                                   in
                                                                let uu____1039
                                                                  =
                                                                  let uu____1042
                                                                    =
                                                                    let uu____1043
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1048
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1053
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1058
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__seq"
                                                                    FStar_Tactics_Basic.seq
                                                                    uu____1043
                                                                    uu____1048
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.seq
                                                                    uu____1053
                                                                    uu____1058
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                  let uu____1071
                                                                    =
                                                                    let uu____1074
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "set_options"
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_options
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1075
                                                                    =
                                                                    let uu____1078
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tc"
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.tc
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1079
                                                                    =
                                                                    let uu____1082
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "unshelve"
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.unshelve
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1083
                                                                    =
                                                                    let uu____1086
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1089
                                                                     ->
                                                                    fun
                                                                    uu____1090
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1093
                                                                    =
                                                                    let uu____1096
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "prune"
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.prune
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1097
                                                                    =
                                                                    let uu____1100
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "addns"
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.addns
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1101
                                                                    =
                                                                    let uu____1104
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "print"
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1105
                                                                    =
                                                                    let uu____1108
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1109
                                                                    =
                                                                    let uu____1112
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1113
                                                                    =
                                                                    let uu____1116
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1117
                                                                    =
                                                                    let uu____1120
                                                                    =
                                                                    let uu____1121
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1126
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1121
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1126
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1135
                                                                    =
                                                                    let uu____1138
                                                                    =
                                                                    let uu____1139
                                                                    =
                                                                    let uu____1151
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1151
                                                                     in
                                                                    let uu____1162
                                                                    =
                                                                    e_tactic_0
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1167
                                                                    =
                                                                    let uu____1179
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1179
                                                                     in
                                                                    let uu____1190
                                                                    =
                                                                    e_tactic_nbe_0
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1139
                                                                    uu____1162
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1167
                                                                    uu____1190
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1217
                                                                    =
                                                                    let uu____1220
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1221
                                                                    =
                                                                    let uu____1224
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1225
                                                                    =
                                                                    let uu____1228
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1229
                                                                    =
                                                                    let uu____1232
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1233
                                                                    =
                                                                    let uu____1236
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1237
                                                                    =
                                                                    let uu____1240
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1241
                                                                    =
                                                                    let uu____1244
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1245
                                                                    =
                                                                    let uu____1248
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "join"
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.join
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1249
                                                                    =
                                                                    let uu____1252
                                                                    =
                                                                    let uu____1253
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1260
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1253
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1260
                                                                     in
                                                                    let uu____1275
                                                                    =
                                                                    let uu____1278
                                                                    =
                                                                    let uu____1279
                                                                    =
                                                                    let uu____1288
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1288
                                                                     in
                                                                    let uu____1299
                                                                    =
                                                                    let uu____1308
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1308
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1279
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1299
                                                                     in
                                                                    let uu____1331
                                                                    =
                                                                    let uu____1334
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                     in
                                                                    let uu____1335
                                                                    =
                                                                    let uu____1338
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                     in
                                                                    let uu____1339
                                                                    =
                                                                    let uu____1342
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_NBEEmbeddings.e_term_view
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1343
                                                                    =
                                                                    let uu____1346
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    let uu____1347
                                                                    =
                                                                    let uu____1350
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    let uu____1351
                                                                    =
                                                                    let uu____1354
                                                                    =
                                                                    let uu____1355
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1360
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1355
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1360
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1369
                                                                    =
                                                                    let uu____1372
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
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
                                                                    let uu____1373
                                                                    =
                                                                    let uu____1376
                                                                    =
                                                                    let uu____1377
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1382
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1377
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1382
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1391
                                                                    =
                                                                    let uu____1394
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
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
                                                                    let uu____1395
                                                                    =
                                                                    let uu____1398
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1399
                                                                    =
                                                                    let uu____1402
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                     in
                                                                    let uu____1403
                                                                    =
                                                                    let uu____1406
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy_nbe
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1407
                                                                    =
                                                                    let uu____1410
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                     in
                                                                    [uu____1410]
                                                                     in
                                                                    uu____1406
                                                                    ::
                                                                    uu____1407
                                                                     in
                                                                    uu____1402
                                                                    ::
                                                                    uu____1403
                                                                     in
                                                                    uu____1398
                                                                    ::
                                                                    uu____1399
                                                                     in
                                                                    uu____1394
                                                                    ::
                                                                    uu____1395
                                                                     in
                                                                    uu____1376
                                                                    ::
                                                                    uu____1391
                                                                     in
                                                                    uu____1372
                                                                    ::
                                                                    uu____1373
                                                                     in
                                                                    uu____1354
                                                                    ::
                                                                    uu____1369
                                                                     in
                                                                    uu____1350
                                                                    ::
                                                                    uu____1351
                                                                     in
                                                                    uu____1346
                                                                    ::
                                                                    uu____1347
                                                                     in
                                                                    uu____1342
                                                                    ::
                                                                    uu____1343
                                                                     in
                                                                    uu____1338
                                                                    ::
                                                                    uu____1339
                                                                     in
                                                                    uu____1334
                                                                    ::
                                                                    uu____1335
                                                                     in
                                                                    uu____1278
                                                                    ::
                                                                    uu____1331
                                                                     in
                                                                    uu____1252
                                                                    ::
                                                                    uu____1275
                                                                     in
                                                                    uu____1248
                                                                    ::
                                                                    uu____1249
                                                                     in
                                                                    uu____1244
                                                                    ::
                                                                    uu____1245
                                                                     in
                                                                    uu____1240
                                                                    ::
                                                                    uu____1241
                                                                     in
                                                                    uu____1236
                                                                    ::
                                                                    uu____1237
                                                                     in
                                                                    uu____1232
                                                                    ::
                                                                    uu____1233
                                                                     in
                                                                    uu____1228
                                                                    ::
                                                                    uu____1229
                                                                     in
                                                                    uu____1224
                                                                    ::
                                                                    uu____1225
                                                                     in
                                                                    uu____1220
                                                                    ::
                                                                    uu____1221
                                                                     in
                                                                    uu____1138
                                                                    ::
                                                                    uu____1217
                                                                     in
                                                                    uu____1120
                                                                    ::
                                                                    uu____1135
                                                                     in
                                                                    uu____1116
                                                                    ::
                                                                    uu____1117
                                                                     in
                                                                    uu____1112
                                                                    ::
                                                                    uu____1113
                                                                     in
                                                                    uu____1108
                                                                    ::
                                                                    uu____1109
                                                                     in
                                                                    uu____1104
                                                                    ::
                                                                    uu____1105
                                                                     in
                                                                    uu____1100
                                                                    ::
                                                                    uu____1101
                                                                     in
                                                                    uu____1096
                                                                    ::
                                                                    uu____1097
                                                                     in
                                                                    uu____1086
                                                                    ::
                                                                    uu____1093
                                                                     in
                                                                    uu____1082
                                                                    ::
                                                                    uu____1083
                                                                     in
                                                                    uu____1078
                                                                    ::
                                                                    uu____1079
                                                                     in
                                                                    uu____1074
                                                                    ::
                                                                    uu____1075
                                                                     in
                                                                  uu____1042
                                                                    ::
                                                                    uu____1071
                                                                   in
                                                                uu____980 ::
                                                                  uu____1039
                                                                 in
                                                              uu____976 ::
                                                                uu____977
                                                               in
                                                            uu____972 ::
                                                              uu____973
                                                             in
                                                          uu____968 ::
                                                            uu____969
                                                           in
                                                        uu____964 ::
                                                          uu____965
                                                         in
                                                      uu____960 :: uu____961
                                                       in
                                                    uu____956 :: uu____957
                                                     in
                                                  uu____952 :: uu____953  in
                                                uu____948 :: uu____949  in
                                              uu____944 :: uu____945  in
                                            uu____940 :: uu____941  in
                                          uu____936 :: uu____937  in
                                        uu____918 :: uu____933  in
                                      uu____900 :: uu____915  in
                                    uu____882 :: uu____897  in
                                  uu____856 :: uu____879  in
                                uu____852 :: uu____853  in
                              uu____808 :: uu____849  in
                            uu____804 :: uu____805  in
                          uu____796 :: uu____801  in
                        uu____736 :: uu____793  in
                      uu____732 :: uu____733  in
                    uu____728 :: uu____729  in
                  uu____724 :: uu____725  in
                uu____706 :: uu____721  in
              uu____688 :: uu____703  in
            uu____684 :: uu____685  in
          uu____680 :: uu____681  in
        uu____676 :: uu____677  in
      uu____672 :: uu____673  in
    let uu____1411 =
      let uu____1414 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____1414
       in
    FStar_List.append uu____669 uu____1411

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            ('Aa -> 'Ar FStar_Tactics_Basic.tac)
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let rng = FStar_Range.dummyRange  in
               let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb  in
               let app =
                 let uu____1444 =
                   let uu____1449 =
                     let uu____1450 = FStar_Syntax_Syntax.as_arg x_tm  in
                     [uu____1450]  in
                   FStar_Syntax_Syntax.mk_Tm_app f uu____1449  in
                 uu____1444 FStar_Pervasives_Native.None rng  in
               unembed_tactic_0 er app ncb)

and unembed_tactic_0 :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings.norm_cb -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun embedded_tac_b  ->
      fun ncb  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let rng = embedded_tac_b.FStar_Syntax_Syntax.pos  in
             let tm =
               let uu____1503 =
                 let uu____1508 =
                   let uu____1509 =
                     let uu____1518 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1518  in
                   [uu____1509]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1508  in
               uu____1503 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1563 = FStar_Options.tactics_nbe ()  in
               if uu____1563
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1582 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1582)
             else ();
             (let result =
                let uu____1585 = primitive_steps ()  in
                norm_f uu____1585 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1589 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1589)
              else ();
              (let res =
                 let uu____1596 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____1596 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____1611 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1611
                     (fun uu____1615  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____1620 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1620
                     (fun uu____1624  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____1627 =
                     let uu____1632 =
                       let uu____1633 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1633
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1632)  in
                   FStar_Errors.raise_error uu____1627
                     (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.iapp_cb ->
          FStar_TypeChecker_NBETerm.t ->
            ('Aa -> 'Ar FStar_Tactics_Basic.tac)
              FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          FStar_Pervasives_Native.Some
            (fun x  ->
               let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
               let app =
                 let uu____1663 =
                   let uu____1664 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                   [uu____1664]  in
                 cb f uu____1663  in
               unembed_tactic_nbe_0 er cb app)

and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.iapp_cb ->
        FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let result =
               let uu____1700 =
                 let uu____1701 =
                   let uu____1706 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1706  in
                 [uu____1701]  in
               cb embedded_tac_b uu____1700  in
             let res =
               let uu____1726 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1726 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1743 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1743
                   (fun uu____1747  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1752 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1752
                   (fun uu____1756  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1759 =
                   let uu____1764 =
                     let uu____1765 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1765
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1764)  in
                 FStar_Errors.raise_error uu____1759
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

let report_implicits :
  'Auu____1774 . 'Auu____1774 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1803 =
               let uu____1804 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1805 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1804 uu____1805 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1803, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____1844 = FStar_ST.op_Bang tacdbg  in
             if uu____1844
             then
               let uu____1864 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1864
             else ());
            (let uu____1866 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1866 with
             | (uu____1879,uu____1880,g) ->
                 ((let uu____1883 = FStar_ST.op_Bang tacdbg  in
                   if uu____1883 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____1909 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1909 with
                   | (env1,uu____1923) ->
                       let env2 =
                         let uu___353_1929 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___353_1929.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___353_1929.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___353_1929.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___353_1929.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___353_1929.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___353_1929.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___353_1929.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___353_1929.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___353_1929.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___353_1929.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___353_1929.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___353_1929.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___353_1929.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___353_1929.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___353_1929.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___353_1929.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___353_1929.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___353_1929.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___353_1929.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___353_1929.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___353_1929.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___353_1929.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___353_1929.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___353_1929.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___353_1929.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___353_1929.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___353_1929.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___353_1929.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___353_1929.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___353_1929.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___353_1929.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___353_1929.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___353_1929.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___353_1929.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___353_1929.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___353_1929.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___353_1929.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___353_1929.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___353_1929.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___353_1929.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___353_1929.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___354_1931 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___354_1931.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___354_1931.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___354_1931.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___354_1931.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___354_1931.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___354_1931.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___354_1931.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___354_1931.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___354_1931.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___354_1931.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___354_1931.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___354_1931.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___354_1931.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___354_1931.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___354_1931.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___354_1931.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___354_1931.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___354_1931.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___354_1931.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___354_1931.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___354_1931.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___354_1931.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___354_1931.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___354_1931.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___354_1931.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___354_1931.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___354_1931.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___354_1931.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___354_1931.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___354_1931.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___354_1931.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___354_1931.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___354_1931.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___354_1931.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___354_1931.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___354_1931.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___354_1931.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___354_1931.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___354_1931.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___354_1931.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___354_1931.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___355_1933 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___355_1933.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___355_1933.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___355_1933.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___355_1933.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___355_1933.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___355_1933.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___355_1933.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___355_1933.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___355_1933.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___355_1933.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___355_1933.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___355_1933.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___355_1933.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___355_1933.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___355_1933.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___355_1933.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___355_1933.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___355_1933.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___355_1933.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___355_1933.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___355_1933.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___355_1933.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___355_1933.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___355_1933.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___355_1933.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___355_1933.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___355_1933.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___355_1933.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___355_1933.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___355_1933.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___355_1933.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___355_1933.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___355_1933.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___355_1933.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___355_1933.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___355_1933.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___355_1933.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___355_1933.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___355_1933.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___355_1933.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___355_1933.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____1935 = FStar_Range.use_range rng_goal  in
                         let uu____1936 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1935 uu____1936  in
                       let uu____1937 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1937 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1975 = FStar_ST.op_Bang tacdbg  in
                              if uu____1975
                              then
                                let uu____1995 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____1995
                              else ());
                             (let uu____1997 =
                                FStar_Util.record_time
                                  (fun uu____2007  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____1997 with
                              | (res,ms) ->
                                  ((let uu____2021 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____2021
                                    then
                                      let uu____2041 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____2042 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____2043 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____2041 uu____2042 uu____2043
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____2051,ps1) ->
                                        ((let uu____2054 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2054
                                          then
                                            let uu____2074 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2074
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____2081 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____2081
                                              then
                                                let uu____2082 =
                                                  let uu____2083 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____2084 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____2083 uu____2084
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____2082
                                                 then ()
                                                 else
                                                   (let uu____2086 =
                                                      let uu____2087 =
                                                        let uu____2088 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2088
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2087
                                                       in
                                                    failwith uu____2086))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2091 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2091
                                          then
                                            let uu____2111 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2111
                                          else ());
                                         (let g1 =
                                            let uu___356_2116 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___356_2116.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___356_2116.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___356_2116.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____2119 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____2119
                                           then
                                             let uu____2139 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____2140 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2139 uu____2140
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____2146 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2146
                                            then
                                              let uu____2166 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____2167 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2166 uu____2167
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2173 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2173
                                            then
                                              let uu____2193 =
                                                let uu____2194 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2194 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____2193
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____2201 =
                                            let uu____2202 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2202 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____2201
                                            "at the time of failure");
                                         (let uu____2203 =
                                            let uu____2208 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2208)
                                             in
                                          FStar_Errors.raise_error uu____2203
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2220 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2226 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2232 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2287 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2327 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2381 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2422 . 'Auu____2422 -> 'Auu____2422 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2450 = FStar_Syntax_Util.head_and_args t  in
        match uu____2450 with
        | (hd1,args) ->
            let uu____2493 =
              let uu____2508 =
                let uu____2509 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2509.FStar_Syntax_Syntax.n  in
              (uu____2508, args)  in
            (match uu____2493 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2524))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2587 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2587 with
                       | (gs,uu____2595) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2602 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2602 with
                       | (gs,uu____2610) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2653 =
                        let uu____2660 =
                          let uu____2663 =
                            let uu____2664 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2664
                             in
                          [uu____2663]  in
                        (FStar_Syntax_Util.t_true, uu____2660)  in
                      Simplified uu____2653
                  | Both  ->
                      let uu____2675 =
                        let uu____2684 =
                          let uu____2687 =
                            let uu____2688 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2688
                             in
                          [uu____2687]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2684)  in
                      Dual uu____2675
                  | Neg  -> Simplified (assertion, []))
             | uu____2701 -> Unchanged t)
  
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
    fun uu___350_2791  ->
      match uu___350_2791 with
      | Unchanged t -> let uu____2797 = f t  in Unchanged uu____2797
      | Simplified (t,gs) ->
          let uu____2804 = let uu____2811 = f t  in (uu____2811, gs)  in
          Simplified uu____2804
      | Dual (tn,tp,gs) ->
          let uu____2821 =
            let uu____2830 = f tn  in
            let uu____2831 = f tp  in (uu____2830, uu____2831, gs)  in
          Dual uu____2821
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2894 = f t1 t2  in Unchanged uu____2894
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2906 = let uu____2913 = f t1 t2  in (uu____2913, gs)
               in
            Simplified uu____2906
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2927 = let uu____2934 = f t1 t2  in (uu____2934, gs)
               in
            Simplified uu____2927
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2953 =
              let uu____2960 = f t1 t2  in
              (uu____2960, (FStar_List.append gs1 gs2))  in
            Simplified uu____2953
        | uu____2963 ->
            let uu____2972 = explode x  in
            (match uu____2972 with
             | (n1,p1,gs1) ->
                 let uu____2990 = explode y  in
                 (match uu____2990 with
                  | (n2,p2,gs2) ->
                      let uu____3008 =
                        let uu____3017 = f n1 n2  in
                        let uu____3018 = f p1 p2  in
                        (uu____3017, uu____3018, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3008))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3090 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3090
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3138  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3180 =
              let uu____3181 = FStar_Syntax_Subst.compress t  in
              uu____3181.FStar_Syntax_Syntax.n  in
            match uu____3180 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3193 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3193 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3219 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3219 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3239;
                   FStar_Syntax_Syntax.vars = uu____3240;_},(p,uu____3242)::
                 (q,uu____3244)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3300 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3300
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3303 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3303 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3317 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3317.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3321;
                   FStar_Syntax_Syntax.vars = uu____3322;_},(p,uu____3324)::
                 (q,uu____3326)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3382 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3382
                   in
                let xq =
                  let uu____3384 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3384
                   in
                let r1 =
                  let uu____3386 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3386 p  in
                let r2 =
                  let uu____3388 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3388 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3395,Unchanged uu____3396) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3414 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3414.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3417 ->
                     let uu____3426 = explode r1  in
                     (match uu____3426 with
                      | (pn,pp,gs1) ->
                          let uu____3444 = explode r2  in
                          (match uu____3444 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3465 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3468 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3465
                                   uu____3468
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3532  ->
                       fun r  ->
                         match uu____3532 with
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
                let uu____3684 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3684 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3724  ->
                            match uu____3724 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3746 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___357_3778 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___357_3778.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___357_3778.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3746 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3806 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3806.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3852 = traverse f pol e t1  in
                let uu____3857 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3857 uu____3852
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___358_3897 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___358_3897.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___358_3897.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3904 =
                f pol e
                  (let uu___359_3908 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___359_3908.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___359_3908.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3904
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___360_3918 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___360_3918.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___360_3918.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3919 = explode rp  in
              (match uu____3919 with
               | (uu____3928,p',gs') ->
                   Dual
                     ((let uu___361_3938 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___361_3938.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___361_3938.FStar_Syntax_Syntax.vars)
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
      (let uu____3981 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____3981);
      (let uu____4002 = FStar_ST.op_Bang tacdbg  in
       if uu____4002
       then
         let uu____4022 =
           let uu____4023 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4023
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4024 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4022
           uu____4024
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4053 =
         let uu____4062 = traverse by_tactic_interp Pos env goal  in
         match uu____4062 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4086 -> failwith "no"  in
       match uu____4053 with
       | (t',gs) ->
           ((let uu____4114 = FStar_ST.op_Bang tacdbg  in
             if uu____4114
             then
               let uu____4134 =
                 let uu____4135 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4135
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4136 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4134 uu____4136
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4184  ->
                    fun g  ->
                      match uu____4184 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4229 =
                              let uu____4232 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____4233 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____4232 uu____4233  in
                            match uu____4229 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4234 =
                                  let uu____4239 =
                                    let uu____4240 =
                                      let uu____4241 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____4241
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____4240
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4239)
                                   in
                                FStar_Errors.raise_error uu____4234
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4244 = FStar_ST.op_Bang tacdbg  in
                            if uu____4244
                            then
                              let uu____4264 = FStar_Util.string_of_int n1
                                 in
                              let uu____4265 =
                                let uu____4266 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____4266
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4264 uu____4265
                            else ());
                           (let gt' =
                              let uu____4269 =
                                let uu____4270 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4270
                                 in
                              FStar_TypeChecker_Util.label uu____4269
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____4271 =
                              let uu____4280 =
                                let uu____4287 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____4287, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____4280 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____4271)))) s
                 gs
                in
             let uu____4302 = s1  in
             match uu____4302 with
             | (uu____4323,gs1) ->
                 let uu____4341 =
                   let uu____4348 = FStar_Options.peek ()  in
                   (env, t', uu____4348)  in
                 uu____4341 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____4361 =
        let uu____4362 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____4362  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4361 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____4363 =
      let uu____4368 =
        let uu____4369 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____4378 =
          let uu____4389 = FStar_Syntax_Syntax.as_arg a  in [uu____4389]  in
        uu____4369 :: uu____4378  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4368  in
    uu____4363 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____4439 =
            let uu____4444 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____4445 =
              let uu____4446 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4446]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____4444 uu____4445  in
          uu____4439 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____4475 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____4475);
           (let uu____4495 =
              let uu____4502 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____4502 env typ
               in
            match uu____4495 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____4517 =
                        let uu____4520 = FStar_Tactics_Types.goal_env g  in
                        let uu____4521 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____4520 uu____4521  in
                      match uu____4517 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____4524 = FStar_ST.op_Bang tacdbg  in
                            if uu____4524
                            then
                              let uu____4544 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____4544
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____4555 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____4555 guard))
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
        ((let uu____4572 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____4572);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____4593 =
            let uu____4600 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____4600 env typ
             in
          match uu____4593 with
          | (gs,w) ->
              ((let uu____4610 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____4614 =
                         let uu____4615 =
                           let uu____4618 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____4619 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____4618 uu____4619  in
                         FStar_Option.isSome uu____4615  in
                       Prims.op_Negation uu____4614) gs
                   in
                if uu____4610
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
                (let uu____4623 = FStar_ST.op_Bang tacdbg  in
                 if uu____4623
                 then
                   let uu____4643 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____4643
                 else ());
                (let uu____4645 =
                   let uu____4650 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____4650 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____4645 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  