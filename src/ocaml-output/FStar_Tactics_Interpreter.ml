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
  
let rec e_tactic_thunk :
  'Ar .
    'Ar FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_Syntax_Embeddings.embedding
  =
  fun er  ->
    let uu____475 =
      FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
    FStar_Syntax_Embeddings.mk_emb
      (fun uu____482  ->
         fun uu____483  ->
           fun uu____484  ->
             fun uu____485  ->
               failwith "Impossible: embedding tactic (thunk)?")
      (fun t  ->
         fun w  ->
           fun cb  ->
             let uu____518 =
               let uu____521 =
                 unembed_tactic_1 FStar_Syntax_Embeddings.e_unit er t cb  in
               uu____521 ()  in
             FStar_Pervasives_Native.Some uu____518) uu____475

and e_tactic_nbe_thunk :
  'Ar .
    'Ar FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_Tactics_Basic.tac FStar_TypeChecker_NBETerm.embedding
  =
  fun er  ->
    let uu____535 =
      FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
    FStar_TypeChecker_NBETerm.mk_emb
      (fun cb  ->
         fun uu____541  ->
           failwith "Impossible: NBE embedding tactic (thunk)?")
      (fun cb  ->
         fun t  ->
           let uu____549 =
             let uu____552 =
               unembed_tactic_nbe_1 FStar_TypeChecker_NBETerm.e_unit er cb t
                in
             uu____552 ()  in
           FStar_Pervasives_Native.Some uu____549)
      (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
      uu____535

and e_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_Syntax_Embeddings.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____567 =
        FStar_Syntax_Embeddings.term_as_fv FStar_Syntax_Syntax.t_unit  in
      FStar_Syntax_Embeddings.mk_emb
        (fun uu____577  ->
           fun uu____578  ->
             fun uu____579  ->
               fun uu____580  -> failwith "Impossible: embedding tactic (1)?")
        (fun t  ->
           fun w  ->
             fun cb  ->
               let uu____615 = unembed_tactic_1 ea er t cb  in
               FStar_Pervasives_Native.Some uu____615) uu____567

and e_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        ('Aa -> 'Ar FStar_Tactics_Basic.tac)
          FStar_TypeChecker_NBETerm.embedding
  =
  fun ea  ->
    fun er  ->
      let uu____635 =
        FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
      FStar_TypeChecker_NBETerm.mk_emb
        (fun cb  ->
           fun uu____644  -> failwith "Impossible: NBE embedding tactic (1)?")
        (fun cb  ->
           fun t  ->
             let uu____654 = unembed_tactic_nbe_1 ea er cb t  in
             FStar_Pervasives_Native.Some uu____654)
        (FStar_TypeChecker_NBETerm.Constant FStar_TypeChecker_NBETerm.Unit)
        uu____635

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
                mktot1' (Prims.parse_int "0") "goals_of"
                  FStar_Tactics_Types.goals_of
                  FStar_Tactics_Embedding.e_proofstate uu____689
                  FStar_Tactics_Types.goals_of
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
                  mktot1' (Prims.parse_int "0") "smt_goals_of"
                    FStar_Tactics_Types.smt_goals_of
                    FStar_Tactics_Embedding.e_proofstate uu____707
                    FStar_Tactics_Types.smt_goals_of
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
                          mktot1' (Prims.parse_int "0") "is_guard"
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal
                            FStar_Syntax_Embeddings.e_bool
                            FStar_Tactics_Types.is_guard
                            FStar_Tactics_Embedding.e_goal_nbe
                            FStar_TypeChecker_NBETerm.e_bool
                           in
                        let uu____737 =
                          let uu____740 =
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
                          let uu____797 =
                            let uu____800 =
                              FStar_Tactics_InterpFuns.mktac2
                                (Prims.parse_int "1") "fail"
                                (fun uu____802  -> FStar_Tactics_Basic.fail)
                                FStar_Syntax_Embeddings.e_any
                                FStar_Syntax_Embeddings.e_string
                                FStar_Syntax_Embeddings.e_any
                                (fun uu____804  -> FStar_Tactics_Basic.fail)
                                FStar_TypeChecker_NBETerm.e_any
                                FStar_TypeChecker_NBETerm.e_string
                                FStar_TypeChecker_NBETerm.e_any
                               in
                            let uu____805 =
                              let uu____808 =
                                let uu____809 =
                                  FStar_Syntax_Embeddings.e_list
                                    FStar_Tactics_Embedding.e_goal
                                   in
                                let uu____814 =
                                  FStar_TypeChecker_NBETerm.e_list
                                    FStar_Tactics_Embedding.e_goal_nbe
                                   in
                                FStar_Tactics_InterpFuns.mktac1
                                  (Prims.parse_int "0") "set_goals"
                                  FStar_Tactics_Basic.set_goals uu____809
                                  FStar_Syntax_Embeddings.e_unit
                                  FStar_Tactics_Basic.set_goals uu____814
                                  FStar_TypeChecker_NBETerm.e_unit
                                 in
                              let uu____823 =
                                let uu____826 =
                                  let uu____827 =
                                    FStar_Syntax_Embeddings.e_list
                                      FStar_Tactics_Embedding.e_goal
                                     in
                                  let uu____832 =
                                    FStar_TypeChecker_NBETerm.e_list
                                      FStar_Tactics_Embedding.e_goal_nbe
                                     in
                                  FStar_Tactics_InterpFuns.mktac1
                                    (Prims.parse_int "0") "set_smt_goals"
                                    FStar_Tactics_Basic.set_smt_goals
                                    uu____827 FStar_Syntax_Embeddings.e_unit
                                    FStar_Tactics_Basic.set_smt_goals
                                    uu____832
                                    FStar_TypeChecker_NBETerm.e_unit
                                   in
                                let uu____841 =
                                  let uu____844 =
                                    FStar_Tactics_InterpFuns.mktac1
                                      (Prims.parse_int "0") "trivial"
                                      FStar_Tactics_Basic.trivial
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Tactics_Basic.trivial
                                      FStar_TypeChecker_NBETerm.e_unit
                                      FStar_TypeChecker_NBETerm.e_unit
                                     in
                                  let uu____845 =
                                    let uu____848 =
                                      let uu____849 =
                                        e_tactic_thunk
                                          FStar_Syntax_Embeddings.e_any
                                         in
                                      let uu____854 =
                                        FStar_Syntax_Embeddings.e_either
                                          FStar_Syntax_Embeddings.e_string
                                          FStar_Syntax_Embeddings.e_any
                                         in
                                      let uu____861 =
                                        e_tactic_nbe_thunk
                                          FStar_TypeChecker_NBETerm.e_any
                                         in
                                      let uu____866 =
                                        FStar_TypeChecker_NBETerm.e_either
                                          FStar_TypeChecker_NBETerm.e_string
                                          FStar_TypeChecker_NBETerm.e_any
                                         in
                                      FStar_Tactics_InterpFuns.mktac2
                                        (Prims.parse_int "1") "catch"
                                        (fun uu____886  ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_Syntax_Embeddings.e_any
                                        uu____849 uu____854
                                        (fun uu____888  ->
                                           FStar_Tactics_Basic.catch)
                                        FStar_TypeChecker_NBETerm.e_any
                                        uu____861 uu____866
                                       in
                                    let uu____889 =
                                      let uu____892 =
                                        FStar_Tactics_InterpFuns.mktac1
                                          (Prims.parse_int "0") "intro"
                                          FStar_Tactics_Basic.intro
                                          FStar_Syntax_Embeddings.e_unit
                                          FStar_Reflection_Embeddings.e_binder
                                          FStar_Tactics_Basic.intro
                                          FStar_TypeChecker_NBETerm.e_unit
                                          FStar_Reflection_NBEEmbeddings.e_binder
                                         in
                                      let uu____893 =
                                        let uu____896 =
                                          let uu____897 =
                                            FStar_Syntax_Embeddings.e_tuple2
                                              FStar_Reflection_Embeddings.e_binder
                                              FStar_Reflection_Embeddings.e_binder
                                             in
                                          let uu____904 =
                                            FStar_TypeChecker_NBETerm.e_tuple2
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                              FStar_Reflection_NBEEmbeddings.e_binder
                                             in
                                          FStar_Tactics_InterpFuns.mktac1
                                            (Prims.parse_int "0") "intro_rec"
                                            FStar_Tactics_Basic.intro_rec
                                            FStar_Syntax_Embeddings.e_unit
                                            uu____897
                                            FStar_Tactics_Basic.intro_rec
                                            FStar_TypeChecker_NBETerm.e_unit
                                            uu____904
                                           in
                                        let uu____919 =
                                          let uu____922 =
                                            let uu____923 =
                                              FStar_Syntax_Embeddings.e_list
                                                FStar_Syntax_Embeddings.e_norm_step
                                               in
                                            let uu____928 =
                                              FStar_TypeChecker_NBETerm.e_list
                                                FStar_TypeChecker_NBETerm.e_norm_step
                                               in
                                            FStar_Tactics_InterpFuns.mktac1
                                              (Prims.parse_int "0") "norm"
                                              FStar_Tactics_Basic.norm
                                              uu____923
                                              FStar_Syntax_Embeddings.e_unit
                                              FStar_Tactics_Basic.norm
                                              uu____928
                                              FStar_TypeChecker_NBETerm.e_unit
                                             in
                                          let uu____937 =
                                            let uu____940 =
                                              let uu____941 =
                                                FStar_Syntax_Embeddings.e_list
                                                  FStar_Syntax_Embeddings.e_norm_step
                                                 in
                                              let uu____946 =
                                                FStar_TypeChecker_NBETerm.e_list
                                                  FStar_TypeChecker_NBETerm.e_norm_step
                                                 in
                                              FStar_Tactics_InterpFuns.mktac3
                                                (Prims.parse_int "0")
                                                "norm_term_env"
                                                FStar_Tactics_Basic.norm_term_env
                                                FStar_Reflection_Embeddings.e_env
                                                uu____941
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Tactics_Basic.norm_term_env
                                                FStar_Reflection_NBEEmbeddings.e_env
                                                uu____946
                                                FStar_Reflection_NBEEmbeddings.e_term
                                                FStar_Reflection_NBEEmbeddings.e_term
                                               in
                                            let uu____955 =
                                              let uu____958 =
                                                let uu____959 =
                                                  FStar_Syntax_Embeddings.e_list
                                                    FStar_Syntax_Embeddings.e_norm_step
                                                   in
                                                let uu____964 =
                                                  FStar_TypeChecker_NBETerm.e_list
                                                    FStar_TypeChecker_NBETerm.e_norm_step
                                                   in
                                                FStar_Tactics_InterpFuns.mktac2
                                                  (Prims.parse_int "0")
                                                  "norm_binder_type"
                                                  FStar_Tactics_Basic.norm_binder_type
                                                  uu____959
                                                  FStar_Reflection_Embeddings.e_binder
                                                  FStar_Syntax_Embeddings.e_unit
                                                  FStar_Tactics_Basic.norm_binder_type
                                                  uu____964
                                                  FStar_Reflection_NBEEmbeddings.e_binder
                                                  FStar_TypeChecker_NBETerm.e_unit
                                                 in
                                              let uu____973 =
                                                let uu____976 =
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
                                                let uu____977 =
                                                  let uu____980 =
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
                                                  let uu____981 =
                                                    let uu____984 =
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
                                                    let uu____985 =
                                                      let uu____988 =
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
                                                      let uu____989 =
                                                        let uu____992 =
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
                                                        let uu____993 =
                                                          let uu____996 =
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
                                                          let uu____997 =
                                                            let uu____1000 =
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
                                                            let uu____1001 =
                                                              let uu____1004
                                                                =
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
                                                              let uu____1005
                                                                =
                                                                let uu____1008
                                                                  =
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
                                                                let uu____1009
                                                                  =
                                                                  let uu____1012
                                                                    =
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
                                                                  let uu____1013
                                                                    =
                                                                    let uu____1016
                                                                    =
                                                                    let uu____1017
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                    let uu____1022
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                    let uu____1027
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                    let uu____1034
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1039
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1044
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac5
                                                                    (Prims.parse_int "2")
                                                                    "divide"
                                                                    (fun
                                                                    uu____1069
                                                                     ->
                                                                    fun
                                                                    uu____1070
                                                                     ->
                                                                    FStar_Tactics_Basic.divide)
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_int
                                                                    uu____1017
                                                                    uu____1022
                                                                    uu____1027
                                                                    (fun
                                                                    uu____1073
                                                                     ->
                                                                    fun
                                                                    uu____1074
                                                                     ->
                                                                    FStar_Tactics_Basic.divide)
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                    uu____1034
                                                                    uu____1039
                                                                    uu____1044
                                                                     in
                                                                    let uu____1075
                                                                    =
                                                                    let uu____1078
                                                                    =
                                                                    let uu____1079
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1084
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1089
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1094
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "seq"
                                                                    FStar_Tactics_Basic.seq
                                                                    uu____1079
                                                                    uu____1084
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.seq
                                                                    uu____1089
                                                                    uu____1094
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1107
                                                                    =
                                                                    let uu____1110
                                                                    =
                                                                    let uu____1111
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_any
                                                                     in
                                                                    let uu____1116
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "focus"
                                                                    (fun
                                                                    uu____1126
                                                                     ->
                                                                    FStar_Tactics_Basic.focus)
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    uu____1111
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1128
                                                                     ->
                                                                    FStar_Tactics_Basic.focus)
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    uu____1116
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1129
                                                                    =
                                                                    let uu____1132
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
                                                                    let uu____1133
                                                                    =
                                                                    let uu____1136
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
                                                                    let uu____1137
                                                                    =
                                                                    let uu____1140
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
                                                                    let uu____1141
                                                                    =
                                                                    let uu____1144
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "unquote"
                                                                    FStar_Tactics_Basic.unquote
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1147
                                                                     ->
                                                                    fun
                                                                    uu____1148
                                                                     ->
                                                                    failwith
                                                                    "NBE unquote")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1151
                                                                    =
                                                                    let uu____1154
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
                                                                    let uu____1155
                                                                    =
                                                                    let uu____1158
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
                                                                    let uu____1159
                                                                    =
                                                                    let uu____1162
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
                                                                    let uu____1163
                                                                    =
                                                                    let uu____1166
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
                                                                    let uu____1167
                                                                    =
                                                                    let uu____1170
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
                                                                    let uu____1171
                                                                    =
                                                                    let uu____1174
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
                                                                    let uu____1175
                                                                    =
                                                                    let uu____1178
                                                                    =
                                                                    let uu____1179
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1184
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "t_pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____1179
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction_nbe
                                                                    uu____1184
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1193
                                                                    =
                                                                    let uu____1196
                                                                    =
                                                                    let uu____1197
                                                                    =
                                                                    let uu____1209
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1209
                                                                     in
                                                                    let uu____1220
                                                                    =
                                                                    e_tactic_thunk
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1225
                                                                    =
                                                                    let uu____1237
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_TypeChecker_NBETerm.e_bool
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    e_tactic_nbe_1
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1237
                                                                     in
                                                                    let uu____1248
                                                                    =
                                                                    e_tactic_nbe_thunk
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1197
                                                                    uu____1220
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____1225
                                                                    uu____1248
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    let uu____1275
                                                                    =
                                                                    let uu____1278
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
                                                                    let uu____1279
                                                                    =
                                                                    let uu____1282
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
                                                                    let uu____1283
                                                                    =
                                                                    let uu____1286
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
                                                                    let uu____1287
                                                                    =
                                                                    let uu____1290
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
                                                                    let uu____1291
                                                                    =
                                                                    let uu____1294
                                                                    =
                                                                    let uu____1295
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1302
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
                                                                    uu____1295
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1302
                                                                     in
                                                                    let uu____1317
                                                                    =
                                                                    let uu____1320
                                                                    =
                                                                    let uu____1321
                                                                    =
                                                                    let uu____1330
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____1330
                                                                     in
                                                                    let uu____1341
                                                                    =
                                                                    let uu____1350
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_tuple2
                                                                    FStar_Reflection_NBEEmbeddings.e_fv
                                                                    FStar_TypeChecker_NBETerm.e_int
                                                                     in
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    uu____1350
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    (Prims.parse_int "0")
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____1321
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                    uu____1341
                                                                     in
                                                                    let uu____1373
                                                                    =
                                                                    let uu____1376
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
                                                                    let uu____1377
                                                                    =
                                                                    let uu____1380
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
                                                                    let uu____1381
                                                                    =
                                                                    let uu____1384
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
                                                                    let uu____1385
                                                                    =
                                                                    let uu____1388
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
                                                                    let uu____1389
                                                                    =
                                                                    let uu____1392
                                                                    =
                                                                    let uu____1393
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____1398
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_option
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "0")
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____1393
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_NBEEmbeddings.e_env
                                                                    uu____1398
                                                                    FStar_Reflection_NBEEmbeddings.e_term
                                                                     in
                                                                    let uu____1407
                                                                    =
                                                                    let uu____1410
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
                                                                    let uu____1411
                                                                    =
                                                                    let uu____1414
                                                                    =
                                                                    let uu____1415
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____1420
                                                                    =
                                                                    FStar_TypeChecker_NBETerm.e_list
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "0")
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____1415
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    uu____1420
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                     in
                                                                    let uu____1429
                                                                    =
                                                                    let uu____1432
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
                                                                    let uu____1433
                                                                    =
                                                                    let uu____1436
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
                                                                    let uu____1437
                                                                    =
                                                                    let uu____1440
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
                                                                    let uu____1441
                                                                    =
                                                                    let uu____1444
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
                                                                    let uu____1445
                                                                    =
                                                                    let uu____1448
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
                                                                    let uu____1449
                                                                    =
                                                                    let uu____1452
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    (Prims.parse_int "1")
                                                                    "lget"
                                                                    FStar_Tactics_Basic.lget
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    (fun
                                                                    uu____1455
                                                                     ->
                                                                    fun
                                                                    uu____1456
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lget` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                     in
                                                                    let uu____1457
                                                                    =
                                                                    let uu____1460
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    (Prims.parse_int "1")
                                                                    "lset"
                                                                    FStar_Tactics_Basic.lset
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_any
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    (fun
                                                                    uu____1464
                                                                     ->
                                                                    fun
                                                                    uu____1465
                                                                     ->
                                                                    fun
                                                                    uu____1466
                                                                     ->
                                                                    FStar_Tactics_Basic.fail
                                                                    "sorry, `lset` does not work in NBE")
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_string
                                                                    FStar_TypeChecker_NBETerm.e_any
                                                                    FStar_TypeChecker_NBETerm.e_unit
                                                                     in
                                                                    [uu____1460]
                                                                     in
                                                                    uu____1452
                                                                    ::
                                                                    uu____1457
                                                                     in
                                                                    uu____1448
                                                                    ::
                                                                    uu____1449
                                                                     in
                                                                    uu____1444
                                                                    ::
                                                                    uu____1445
                                                                     in
                                                                    uu____1440
                                                                    ::
                                                                    uu____1441
                                                                     in
                                                                    uu____1436
                                                                    ::
                                                                    uu____1437
                                                                     in
                                                                    uu____1432
                                                                    ::
                                                                    uu____1433
                                                                     in
                                                                    uu____1414
                                                                    ::
                                                                    uu____1429
                                                                     in
                                                                    uu____1410
                                                                    ::
                                                                    uu____1411
                                                                     in
                                                                    uu____1392
                                                                    ::
                                                                    uu____1407
                                                                     in
                                                                    uu____1388
                                                                    ::
                                                                    uu____1389
                                                                     in
                                                                    uu____1384
                                                                    ::
                                                                    uu____1385
                                                                     in
                                                                    uu____1380
                                                                    ::
                                                                    uu____1381
                                                                     in
                                                                    uu____1376
                                                                    ::
                                                                    uu____1377
                                                                     in
                                                                    uu____1320
                                                                    ::
                                                                    uu____1373
                                                                     in
                                                                    uu____1294
                                                                    ::
                                                                    uu____1317
                                                                     in
                                                                    uu____1290
                                                                    ::
                                                                    uu____1291
                                                                     in
                                                                    uu____1286
                                                                    ::
                                                                    uu____1287
                                                                     in
                                                                    uu____1282
                                                                    ::
                                                                    uu____1283
                                                                     in
                                                                    uu____1278
                                                                    ::
                                                                    uu____1279
                                                                     in
                                                                    uu____1196
                                                                    ::
                                                                    uu____1275
                                                                     in
                                                                    uu____1178
                                                                    ::
                                                                    uu____1193
                                                                     in
                                                                    uu____1174
                                                                    ::
                                                                    uu____1175
                                                                     in
                                                                    uu____1170
                                                                    ::
                                                                    uu____1171
                                                                     in
                                                                    uu____1166
                                                                    ::
                                                                    uu____1167
                                                                     in
                                                                    uu____1162
                                                                    ::
                                                                    uu____1163
                                                                     in
                                                                    uu____1158
                                                                    ::
                                                                    uu____1159
                                                                     in
                                                                    uu____1154
                                                                    ::
                                                                    uu____1155
                                                                     in
                                                                    uu____1144
                                                                    ::
                                                                    uu____1151
                                                                     in
                                                                    uu____1140
                                                                    ::
                                                                    uu____1141
                                                                     in
                                                                    uu____1136
                                                                    ::
                                                                    uu____1137
                                                                     in
                                                                    uu____1132
                                                                    ::
                                                                    uu____1133
                                                                     in
                                                                    uu____1110
                                                                    ::
                                                                    uu____1129
                                                                     in
                                                                    uu____1078
                                                                    ::
                                                                    uu____1107
                                                                     in
                                                                    uu____1016
                                                                    ::
                                                                    uu____1075
                                                                     in
                                                                  uu____1012
                                                                    ::
                                                                    uu____1013
                                                                   in
                                                                uu____1008 ::
                                                                  uu____1009
                                                                 in
                                                              uu____1004 ::
                                                                uu____1005
                                                               in
                                                            uu____1000 ::
                                                              uu____1001
                                                             in
                                                          uu____996 ::
                                                            uu____997
                                                           in
                                                        uu____992 ::
                                                          uu____993
                                                         in
                                                      uu____988 :: uu____989
                                                       in
                                                    uu____984 :: uu____985
                                                     in
                                                  uu____980 :: uu____981  in
                                                uu____976 :: uu____977  in
                                              uu____958 :: uu____973  in
                                            uu____940 :: uu____955  in
                                          uu____922 :: uu____937  in
                                        uu____896 :: uu____919  in
                                      uu____892 :: uu____893  in
                                    uu____848 :: uu____889  in
                                  uu____844 :: uu____845  in
                                uu____826 :: uu____841  in
                              uu____808 :: uu____823  in
                            uu____800 :: uu____805  in
                          uu____740 :: uu____797  in
                        uu____736 :: uu____737  in
                      uu____732 :: uu____733  in
                    uu____728 :: uu____729  in
                  uu____724 :: uu____725  in
                uu____706 :: uu____721  in
              uu____688 :: uu____703  in
            uu____684 :: uu____685  in
          uu____680 :: uu____681  in
        uu____676 :: uu____677  in
      uu____672 :: uu____673  in
    let uu____1467 =
      let uu____1470 = FStar_Tactics_InterpFuns.native_tactics_steps ()  in
      FStar_List.append FStar_Reflection_Interpreter.reflection_primops
        uu____1470
       in
    FStar_List.append uu____669 uu____1467

and unembed_tactic_1 :
  'Aa 'Ar .
    'Aa FStar_Syntax_Embeddings.embedding ->
      'Ar FStar_Syntax_Embeddings.embedding ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Embeddings.norm_cb ->
            'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea  ->
    fun er  ->
      fun f  ->
        fun ncb  ->
          fun x  ->
            let rng = FStar_Range.dummyRange  in
            let x_tm = FStar_Tactics_InterpFuns.embed ea rng x ncb  in
            let app =
              let uu____1491 =
                let uu____1496 =
                  let uu____1497 = FStar_Syntax_Syntax.as_arg x_tm  in
                  [uu____1497]  in
                FStar_Syntax_Syntax.mk_Tm_app f uu____1496  in
              uu____1491 FStar_Pervasives_Native.None rng  in
            unembed_tactic_0 er app ncb

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
             let embedded_tac_b1 = FStar_Syntax_Util.mk_reify embedded_tac_b
                in
             let tm =
               let uu____1554 =
                 let uu____1559 =
                   let uu____1560 =
                     let uu____1569 =
                       FStar_Tactics_InterpFuns.embed
                         FStar_Tactics_Embedding.e_proofstate rng proof_state
                         ncb
                        in
                     FStar_Syntax_Syntax.as_arg uu____1569  in
                   [uu____1560]  in
                 FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b1 uu____1559  in
               uu____1554 FStar_Pervasives_Native.None rng  in
             let steps =
               [FStar_TypeChecker_Env.Weak;
               FStar_TypeChecker_Env.Reify;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.UnfoldTac;
               FStar_TypeChecker_Env.Primops;
               FStar_TypeChecker_Env.Unascribe]  in
             let norm_f =
               let uu____1614 = FStar_Options.tactics_nbe ()  in
               if uu____1614
               then FStar_TypeChecker_NBE.normalize
               else
                 FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                in
             if proof_state.FStar_Tactics_Types.tac_verb_dbg
             then
               (let uu____1633 = FStar_Syntax_Print.term_to_string tm  in
                FStar_Util.print1 "Starting normalizer with %s\n" uu____1633)
             else ();
             (let result =
                let uu____1636 = primitive_steps ()  in
                norm_f uu____1636 steps
                  proof_state.FStar_Tactics_Types.main_context tm
                 in
              if proof_state.FStar_Tactics_Types.tac_verb_dbg
              then
                (let uu____1640 = FStar_Syntax_Print.term_to_string result
                    in
                 FStar_Util.print1 "Reduced tactic: got %s\n" uu____1640)
              else ();
              (let res =
                 let uu____1647 = FStar_Tactics_Embedding.e_result eb  in
                 FStar_Tactics_InterpFuns.unembed uu____1647 result ncb  in
               match res with
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                   (b,ps)) ->
                   let uu____1662 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1662
                     (fun uu____1666  -> FStar_Tactics_Basic.ret b)
               | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                   (msg,ps)) ->
                   let uu____1671 = FStar_Tactics_Basic.set ps  in
                   FStar_Tactics_Basic.bind uu____1671
                     (fun uu____1675  -> FStar_Tactics_Basic.fail msg)
               | FStar_Pervasives_Native.None  ->
                   let uu____1678 =
                     let uu____1683 =
                       let uu____1684 =
                         FStar_Syntax_Print.term_to_string result  in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____1684
                        in
                     (FStar_Errors.Fatal_TacticGotStuck, uu____1683)  in
                   FStar_Errors.raise_error uu____1678
                     (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_nbe_1 :
  'Aa 'Ar .
    'Aa FStar_TypeChecker_NBETerm.embedding ->
      'Ar FStar_TypeChecker_NBETerm.embedding ->
        FStar_TypeChecker_NBETerm.nbe_cbs ->
          FStar_TypeChecker_NBETerm.t -> 'Aa -> 'Ar FStar_Tactics_Basic.tac
  =
  fun ea  ->
    fun er  ->
      fun cb  ->
        fun f  ->
          fun x  ->
            let x_tm = FStar_TypeChecker_NBETerm.embed ea cb x  in
            let app =
              let uu____1698 =
                let uu____1699 = FStar_TypeChecker_NBETerm.as_arg x_tm  in
                [uu____1699]  in
              FStar_TypeChecker_NBETerm.iapp_cb cb f uu____1698  in
            unembed_tactic_nbe_0 er cb app

and unembed_tactic_nbe_0 :
  'Ab .
    'Ab FStar_TypeChecker_NBETerm.embedding ->
      FStar_TypeChecker_NBETerm.nbe_cbs ->
        FStar_TypeChecker_NBETerm.t -> 'Ab FStar_Tactics_Basic.tac
  =
  fun eb  ->
    fun cb  ->
      fun embedded_tac_b  ->
        FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
          (fun proof_state  ->
             let result =
               let uu____1725 =
                 let uu____1726 =
                   let uu____1731 =
                     FStar_TypeChecker_NBETerm.embed
                       FStar_Tactics_Embedding.e_proofstate_nbe cb
                       proof_state
                      in
                   FStar_TypeChecker_NBETerm.as_arg uu____1731  in
                 [uu____1726]  in
               FStar_TypeChecker_NBETerm.iapp_cb cb embedded_tac_b uu____1725
                in
             let res =
               let uu____1745 = FStar_Tactics_Embedding.e_result_nbe eb  in
               FStar_TypeChecker_NBETerm.unembed uu____1745 cb result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1758 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1758
                   (fun uu____1762  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1767 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1767
                   (fun uu____1771  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1774 =
                   let uu____1779 =
                     let uu____1780 =
                       FStar_TypeChecker_NBETerm.t_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck (in NBE)! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1780
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1779)  in
                 FStar_Errors.raise_error uu____1774
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)

let report_implicits :
  'Auu____1789 . 'Auu____1789 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1818 =
               let uu____1819 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1820 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1819 uu____1820 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1818, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____1859 = FStar_ST.op_Bang tacdbg  in
             if uu____1859
             then
               let uu____1879 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1879
             else ());
            (let uu____1881 = FStar_TypeChecker_TcTerm.tc_tactic env tactic
                in
             match uu____1881 with
             | (uu____1894,uu____1895,g) ->
                 ((let uu____1898 = FStar_ST.op_Bang tacdbg  in
                   if uu____1898 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_1 FStar_Syntax_Embeddings.e_unit
                       FStar_Syntax_Embeddings.e_unit tactic
                       FStar_Syntax_Embeddings.id_norm_cb
                      in
                   let uu____1928 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1928 with
                   | (env1,uu____1942) ->
                       let env2 =
                         let uu___353_1948 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___353_1948.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___353_1948.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___353_1948.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___353_1948.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___353_1948.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___353_1948.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___353_1948.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___353_1948.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___353_1948.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___353_1948.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___353_1948.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___353_1948.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___353_1948.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___353_1948.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___353_1948.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___353_1948.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___353_1948.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___353_1948.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___353_1948.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___353_1948.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___353_1948.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___353_1948.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___353_1948.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___353_1948.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___353_1948.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___353_1948.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___353_1948.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___353_1948.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___353_1948.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___353_1948.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___353_1948.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___353_1948.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___353_1948.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___353_1948.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___353_1948.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___353_1948.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___353_1948.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___353_1948.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___353_1948.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___353_1948.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___353_1948.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___354_1950 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___354_1950.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___354_1950.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___354_1950.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___354_1950.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___354_1950.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___354_1950.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___354_1950.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___354_1950.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___354_1950.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___354_1950.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___354_1950.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___354_1950.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___354_1950.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___354_1950.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___354_1950.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___354_1950.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___354_1950.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___354_1950.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___354_1950.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___354_1950.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___354_1950.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___354_1950.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___354_1950.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___354_1950.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___354_1950.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___354_1950.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___354_1950.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___354_1950.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___354_1950.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___354_1950.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___354_1950.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___354_1950.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___354_1950.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___354_1950.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___354_1950.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___354_1950.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___354_1950.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___354_1950.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___354_1950.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___354_1950.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___354_1950.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___355_1952 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___355_1952.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___355_1952.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___355_1952.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___355_1952.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___355_1952.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___355_1952.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___355_1952.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___355_1952.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___355_1952.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___355_1952.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___355_1952.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___355_1952.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___355_1952.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___355_1952.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___355_1952.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___355_1952.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___355_1952.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___355_1952.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___355_1952.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___355_1952.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___355_1952.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___355_1952.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___355_1952.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___355_1952.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___355_1952.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___355_1952.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___355_1952.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___355_1952.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___355_1952.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___355_1952.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___355_1952.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___355_1952.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___355_1952.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___355_1952.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___355_1952.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___355_1952.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___355_1952.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___355_1952.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___355_1952.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___355_1952.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___355_1952.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____1954 = FStar_Range.use_range rng_goal  in
                         let uu____1955 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1954 uu____1955  in
                       let uu____1956 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1956 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1994 = FStar_ST.op_Bang tacdbg  in
                              if uu____1994
                              then
                                let uu____2014 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____2014
                              else ());
                             (let uu____2016 =
                                FStar_Util.record_time
                                  (fun uu____2027  ->
                                     let uu____2028 = tau ()  in
                                     FStar_Tactics_Basic.run_safe uu____2028
                                       ps)
                                 in
                              match uu____2016 with
                              | (res,ms) ->
                                  ((let uu____2044 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____2044
                                    then
                                      let uu____2064 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____2065 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____2066 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____2064 uu____2065 uu____2066
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____2074,ps1) ->
                                        ((let uu____2077 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2077
                                          then
                                            let uu____2097 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____2097
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____2104 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____2104
                                              then
                                                let uu____2105 =
                                                  let uu____2106 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____2107 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt_force
                                                    uu____2106 uu____2107
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____2105
                                                 then ()
                                                 else
                                                   (let uu____2109 =
                                                      let uu____2110 =
                                                        let uu____2111 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____2111
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____2110
                                                       in
                                                    failwith uu____2109))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____2114 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____2114
                                          then
                                            let uu____2134 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____2134
                                          else ());
                                         (let g1 =
                                            let uu___356_2139 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___356_2139.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___356_2139.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___356_2139.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____2142 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____2142
                                           then
                                             let uu____2162 =
                                               FStar_Util.string_of_int
                                                 (FStar_List.length
                                                    ps1.FStar_Tactics_Types.all_implicits)
                                                in
                                             let uu____2163 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print2
                                               "Checked %s implicits (1): %s\n"
                                               uu____2162 uu____2163
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____2169 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2169
                                            then
                                              let uu____2189 =
                                                FStar_Util.string_of_int
                                                  (FStar_List.length
                                                     ps1.FStar_Tactics_Types.all_implicits)
                                                 in
                                              let uu____2190 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print2
                                                "Checked %s implicits (2): %s\n"
                                                uu____2189 uu____2190
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           (let uu____2196 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____2196
                                            then
                                              let uu____2216 =
                                                let uu____2217 =
                                                  FStar_TypeChecker_Cfg.psc_subst
                                                    ps1.FStar_Tactics_Types.psc
                                                   in
                                                FStar_Tactics_Types.subst_proof_state
                                                  uu____2217 ps1
                                                 in
                                              FStar_Tactics_Basic.dump_proofstate
                                                uu____2216
                                                "at the finish line"
                                            else ());
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____2224 =
                                            let uu____2225 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____2225 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____2224
                                            "at the time of failure");
                                         (let uu____2226 =
                                            let uu____2231 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____2231)
                                             in
                                          FStar_Errors.raise_error uu____2226
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____2243 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____2249 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2255 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2310 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2350 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2404 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____2445 . 'Auu____2445 -> 'Auu____2445 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2473 = FStar_Syntax_Util.head_and_args t  in
        match uu____2473 with
        | (hd1,args) ->
            let uu____2516 =
              let uu____2531 =
                let uu____2532 = FStar_Syntax_Util.un_uinst hd1  in
                uu____2532.FStar_Syntax_Syntax.n  in
              (uu____2531, args)  in
            (match uu____2516 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2547))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2610 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2610 with
                       | (gs,uu____2618) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2625 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____2625 with
                       | (gs,uu____2633) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2676 =
                        let uu____2683 =
                          let uu____2686 =
                            let uu____2687 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2687
                             in
                          [uu____2686]  in
                        (FStar_Syntax_Util.t_true, uu____2683)  in
                      Simplified uu____2676
                  | Both  ->
                      let uu____2698 =
                        let uu____2707 =
                          let uu____2710 =
                            let uu____2711 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2711
                             in
                          [uu____2710]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2707)  in
                      Dual uu____2698
                  | Neg  -> Simplified (assertion, []))
             | uu____2724 -> Unchanged t)
  
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
    fun uu___350_2814  ->
      match uu___350_2814 with
      | Unchanged t -> let uu____2820 = f t  in Unchanged uu____2820
      | Simplified (t,gs) ->
          let uu____2827 = let uu____2834 = f t  in (uu____2834, gs)  in
          Simplified uu____2827
      | Dual (tn,tp,gs) ->
          let uu____2844 =
            let uu____2853 = f tn  in
            let uu____2854 = f tp  in (uu____2853, uu____2854, gs)  in
          Dual uu____2844
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2917 = f t1 t2  in Unchanged uu____2917
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2929 = let uu____2936 = f t1 t2  in (uu____2936, gs)
               in
            Simplified uu____2929
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2950 = let uu____2957 = f t1 t2  in (uu____2957, gs)
               in
            Simplified uu____2950
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2976 =
              let uu____2983 = f t1 t2  in
              (uu____2983, (FStar_List.append gs1 gs2))  in
            Simplified uu____2976
        | uu____2986 ->
            let uu____2995 = explode x  in
            (match uu____2995 with
             | (n1,p1,gs1) ->
                 let uu____3013 = explode y  in
                 (match uu____3013 with
                  | (n2,p2,gs2) ->
                      let uu____3031 =
                        let uu____3040 = f n1 n2  in
                        let uu____3041 = f p1 p2  in
                        (uu____3040, uu____3041, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____3031))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3113 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____3113
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3161  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3203 =
              let uu____3204 = FStar_Syntax_Subst.compress t  in
              uu____3204.FStar_Syntax_Syntax.n  in
            match uu____3203 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____3216 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____3216 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____3242 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____3242 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3262;
                   FStar_Syntax_Syntax.vars = uu____3263;_},(p,uu____3265)::
                 (q,uu____3267)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3323 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3323
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____3326 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____3326 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3340 = FStar_Syntax_Util.mk_imp l r  in
                       uu____3340.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3344;
                   FStar_Syntax_Syntax.vars = uu____3345;_},(p,uu____3347)::
                 (q,uu____3349)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3405 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3405
                   in
                let xq =
                  let uu____3407 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3407
                   in
                let r1 =
                  let uu____3409 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____3409 p  in
                let r2 =
                  let uu____3411 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____3411 q  in
                (match (r1, r2) with
                 | (Unchanged uu____3418,Unchanged uu____3419) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3437 = FStar_Syntax_Util.mk_iff l r  in
                            uu____3437.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3440 ->
                     let uu____3449 = explode r1  in
                     (match uu____3449 with
                      | (pn,pp,gs1) ->
                          let uu____3467 = explode r2  in
                          (match uu____3467 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3488 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____3491 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____3488
                                   uu____3491
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3555  ->
                       fun r  ->
                         match uu____3555 with
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
                let uu____3707 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3707 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3747  ->
                            match uu____3747 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3769 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___357_3801 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___357_3801.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___357_3801.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3769 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3829 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3829.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3875 = traverse f pol e t1  in
                let uu____3880 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3880 uu____3875
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___358_3920 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___358_3920.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___358_3920.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3927 =
                f pol e
                  (let uu___359_3931 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___359_3931.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___359_3931.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3927
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___360_3941 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___360_3941.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___360_3941.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3942 = explode rp  in
              (match uu____3942 with
               | (uu____3951,p',gs') ->
                   Dual
                     ((let uu___361_3961 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___361_3961.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___361_3961.FStar_Syntax_Syntax.vars)
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
      (let uu____4004 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____4004);
      (let uu____4025 = FStar_ST.op_Bang tacdbg  in
       if uu____4025
       then
         let uu____4045 =
           let uu____4046 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____4046
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____4047 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4045
           uu____4047
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____4076 =
         let uu____4085 = traverse by_tactic_interp Pos env goal  in
         match uu____4085 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4109 -> failwith "no"  in
       match uu____4076 with
       | (t',gs) ->
           ((let uu____4137 = FStar_ST.op_Bang tacdbg  in
             if uu____4137
             then
               let uu____4157 =
                 let uu____4158 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____4158
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____4159 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4157 uu____4159
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4207  ->
                    fun g  ->
                      match uu____4207 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4252 =
                              let uu____4255 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____4256 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____4255 uu____4256  in
                            match uu____4252 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4257 =
                                  let uu____4262 =
                                    let uu____4263 =
                                      let uu____4264 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____4264
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____4263
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____4262)
                                   in
                                FStar_Errors.raise_error uu____4257
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____4267 = FStar_ST.op_Bang tacdbg  in
                            if uu____4267
                            then
                              let uu____4287 = FStar_Util.string_of_int n1
                                 in
                              let uu____4288 =
                                let uu____4289 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____4289
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4287 uu____4288
                            else ());
                           (let gt' =
                              let uu____4292 =
                                let uu____4293 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____4293
                                 in
                              FStar_TypeChecker_Util.label uu____4292
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____4294 =
                              let uu____4303 =
                                let uu____4310 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____4310, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____4303 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____4294)))) s
                 gs
                in
             let uu____4325 = s1  in
             match uu____4325 with
             | (uu____4346,gs1) ->
                 let uu____4364 =
                   let uu____4371 = FStar_Options.peek ()  in
                   (env, t', uu____4371)  in
                 uu____4364 :: gs1)))
  
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
          let uu____4393 =
            let uu____4398 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____4399 =
              let uu____4400 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4400]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____4398 uu____4399  in
          uu____4393 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____4429 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____4429);
           (let uu____4449 =
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos tau env typ
               in
            match uu____4449 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____4470 =
                        let uu____4473 = FStar_Tactics_Types.goal_env g  in
                        let uu____4474 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____4473 uu____4474  in
                      match uu____4470 with
                      | FStar_Pervasives_Native.Some vc ->
                          ((let uu____4477 = FStar_ST.op_Bang tacdbg  in
                            if uu____4477
                            then
                              let uu____4497 =
                                FStar_Syntax_Print.term_to_string vc  in
                              FStar_Util.print1 "Synthesis left a goal: %s\n"
                                uu____4497
                            else ());
                           (let guard =
                              {
                                FStar_TypeChecker_Env.guard_f =
                                  (FStar_TypeChecker_Common.NonTrivial vc);
                                FStar_TypeChecker_Env.deferred = [];
                                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                                FStar_TypeChecker_Env.implicits = []
                              }  in
                            let uu____4508 = FStar_Tactics_Types.goal_env g
                               in
                            FStar_TypeChecker_Rel.force_trivial_guard
                              uu____4508 guard))
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
        ((let uu____4525 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____4525);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____4546 =
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos tau env typ
             in
          match uu____4546 with
          | (gs,w) ->
              ((let uu____4562 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____4566 =
                         let uu____4567 =
                           let uu____4570 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____4571 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____4570 uu____4571  in
                         FStar_Option.isSome uu____4567  in
                       Prims.op_Negation uu____4566) gs
                   in
                if uu____4562
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
                (let uu____4575 = FStar_ST.op_Bang tacdbg  in
                 if uu____4575
                 then
                   let uu____4595 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____4595
                 else ());
                (let uu____4597 =
                   let uu____4602 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Tactics_InterpFuns.unembed uu____4602 w1
                     FStar_Syntax_Embeddings.id_norm_cb
                    in
                 match uu____4597 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  