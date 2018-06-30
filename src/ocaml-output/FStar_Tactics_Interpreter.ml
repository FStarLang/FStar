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
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____208)::[] ->
          let uu____233 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____233
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____241 =
                 let uu____242 = FStar_TypeChecker_Cfg.psc_range psc  in
                 let uu____243 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____242 uu____243
                  in
               FStar_Pervasives_Native.Some uu____241)
      | uu____244 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____248 = FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"
         in
      let uu____249 =
        let uu____256 = FStar_Ident.lid_of_str "_"  in
        FStar_TypeChecker_NBETerm.dummy_interp uu____256  in
      {
        FStar_TypeChecker_Cfg.name = uu____248;
        FStar_TypeChecker_Cfg.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
        FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
        FStar_TypeChecker_Cfg.strong_reduction_ok = false;
        FStar_TypeChecker_Cfg.requires_binder_substitution = false;
        FStar_TypeChecker_Cfg.interpretation = decr_depth_interp;
        FStar_TypeChecker_Cfg.interpretation_nbe = uu____249
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____273)::[] ->
          let uu____298 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____298
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____306 =
                 let uu____307 = FStar_TypeChecker_Cfg.psc_range psc  in
                 let uu____308 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____307 uu____308
                  in
               FStar_Pervasives_Native.Some uu____306)
      | uu____309 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____313 = FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"
         in
      let uu____314 =
        let uu____321 = FStar_Ident.lid_of_str "_"  in
        FStar_TypeChecker_NBETerm.dummy_interp uu____321  in
      {
        FStar_TypeChecker_Cfg.name = uu____313;
        FStar_TypeChecker_Cfg.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
        FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
        FStar_TypeChecker_Cfg.strong_reduction_ok = false;
        FStar_TypeChecker_Cfg.requires_binder_substitution = false;
        FStar_TypeChecker_Cfg.interpretation = incr_depth_interp;
        FStar_TypeChecker_Cfg.interpretation_nbe = uu____314
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____338)::[] ->
          let uu____363 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____363
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____372 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____391)::(r,uu____393)::[] ->
          let uu____434 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____434
            (fun ps1  ->
               let uu____440 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r
                  in
               FStar_Util.bind_opt uu____440
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____448 =
                      let uu____449 = FStar_TypeChecker_Cfg.psc_range psc  in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____449 ps'
                       in
                    FStar_Pervasives_Native.Some uu____448))
      | uu____450 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____469)::(b,uu____471)::[] ->
          let uu____512 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t
             in
          FStar_Util.bind_opt uu____512
            (fun env  ->
               let uu____518 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b
                  in
               FStar_Util.bind_opt uu____518
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____538 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____538))
      | uu____539 -> failwith "Unexpected application of push_binder"  in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      let uu____544 =
        let uu____551 = FStar_Ident.lid_of_str "_"  in
        FStar_TypeChecker_NBETerm.dummy_interp uu____551  in
      {
        FStar_TypeChecker_Cfg.name = nm;
        FStar_TypeChecker_Cfg.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
        FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
        FStar_TypeChecker_Cfg.strong_reduction_ok = false;
        FStar_TypeChecker_Cfg.requires_binder_substitution = false;
        FStar_TypeChecker_Cfg.interpretation = set_proofstate_range_interp;
        FStar_TypeChecker_Cfg.interpretation_nbe = uu____544
      }  in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"  in
      let uu____554 =
        let uu____561 = FStar_Ident.lid_of_str "_"  in
        FStar_TypeChecker_NBETerm.dummy_interp uu____561  in
      {
        FStar_TypeChecker_Cfg.name = nm;
        FStar_TypeChecker_Cfg.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
        FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
        FStar_TypeChecker_Cfg.strong_reduction_ok = false;
        FStar_TypeChecker_Cfg.requires_binder_substitution = true;
        FStar_TypeChecker_Cfg.interpretation = tracepoint_interp;
        FStar_TypeChecker_Cfg.interpretation_nbe = uu____554
      }  in
    let push_binder_step =
      let nm =
        FStar_Tactics_Embedding.fstar_tactics_lid'
          ["Builtins"; "push_binder"]
         in
      let uu____564 =
        let uu____571 = FStar_Ident.lid_of_str "_"  in
        FStar_TypeChecker_NBETerm.dummy_interp uu____571  in
      {
        FStar_TypeChecker_Cfg.name = nm;
        FStar_TypeChecker_Cfg.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0");
        FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None;
        FStar_TypeChecker_Cfg.strong_reduction_ok = false;
        FStar_TypeChecker_Cfg.requires_binder_substitution = true;
        FStar_TypeChecker_Cfg.interpretation = push_binder_interp;
        FStar_TypeChecker_Cfg.interpretation_nbe = uu____564
      }  in
    let uu____572 =
      let uu____575 =
        FStar_Tactics_InterpFuns.mktac2 "fail"
          (fun uu____577  -> FStar_Tactics_Basic.fail)
          FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string
          FStar_Syntax_Embeddings.e_any
         in
      let uu____578 =
        let uu____581 =
          FStar_Tactics_InterpFuns.mktac1 "trivial"
            FStar_Tactics_Basic.trivial FStar_Syntax_Embeddings.e_unit
            FStar_Syntax_Embeddings.e_unit
           in
        let uu____582 =
          let uu____585 =
            let uu____586 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____591 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            FStar_Tactics_InterpFuns.mktac2 "__trytac"
              (fun uu____601  -> FStar_Tactics_Basic.trytac)
              FStar_Syntax_Embeddings.e_any uu____586 uu____591
             in
          let uu____602 =
            let uu____605 =
              FStar_Tactics_InterpFuns.mktac1 "intro"
                FStar_Tactics_Basic.intro FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_Embeddings.e_binder
               in
            let uu____606 =
              let uu____609 =
                let uu____610 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                FStar_Tactics_InterpFuns.mktac1 "intro_rec"
                  FStar_Tactics_Basic.intro_rec
                  FStar_Syntax_Embeddings.e_unit uu____610
                 in
              let uu____621 =
                let uu____624 =
                  let uu____625 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  FStar_Tactics_InterpFuns.mktac1 "norm"
                    FStar_Tactics_Basic.norm uu____625
                    FStar_Syntax_Embeddings.e_unit
                   in
                let uu____632 =
                  let uu____635 =
                    let uu____636 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    FStar_Tactics_InterpFuns.mktac3 "norm_term_env"
                      FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Embeddings.e_env uu____636
                      FStar_Reflection_Embeddings.e_term
                      FStar_Reflection_Embeddings.e_term
                     in
                  let uu____643 =
                    let uu____646 =
                      let uu____647 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      FStar_Tactics_InterpFuns.mktac2 "norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____647
                        FStar_Reflection_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit
                       in
                    let uu____654 =
                      let uu____657 =
                        FStar_Tactics_InterpFuns.mktac2 "rename_to"
                          FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_unit
                         in
                      let uu____658 =
                        let uu____661 =
                          FStar_Tactics_InterpFuns.mktac1 "binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                           in
                        let uu____662 =
                          let uu____665 =
                            FStar_Tactics_InterpFuns.mktac1 "revert"
                              FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____666 =
                            let uu____669 =
                              FStar_Tactics_InterpFuns.mktac1 "clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                               in
                            let uu____670 =
                              let uu____673 =
                                FStar_Tactics_InterpFuns.mktac1 "clear"
                                  FStar_Tactics_Basic.clear
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                 in
                              let uu____674 =
                                let uu____677 =
                                  FStar_Tactics_InterpFuns.mktac1 "rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____678 =
                                  let uu____681 =
                                    FStar_Tactics_InterpFuns.mktac1 "smt"
                                      FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____682 =
                                    let uu____685 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        "refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____686 =
                                      let uu____689 =
                                        FStar_Tactics_InterpFuns.mktac2
                                          "t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____690 =
                                        let uu____693 =
                                          FStar_Tactics_InterpFuns.mktac1
                                            "apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        let uu____694 =
                                          let uu____697 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              "apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_unit
                                             in
                                          let uu____698 =
                                            let uu____701 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                "apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_unit
                                               in
                                            let uu____702 =
                                              let uu____705 =
                                                let uu____706 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____711 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____716 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                FStar_Tactics_InterpFuns.mktac5
                                                  "__divide"
                                                  (fun uu____733  ->
                                                     fun uu____734  ->
                                                       FStar_Tactics_Basic.divide)
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_int
                                                  uu____706 uu____711
                                                  uu____716
                                                 in
                                              let uu____735 =
                                                let uu____738 =
                                                  let uu____739 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____744 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac2
                                                    "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    uu____739 uu____744
                                                    FStar_Syntax_Embeddings.e_unit
                                                   in
                                                let uu____753 =
                                                  let uu____756 =
                                                    FStar_Tactics_InterpFuns.mktac1
                                                      "set_options"
                                                      FStar_Tactics_Basic.set_options
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____757 =
                                                    let uu____760 =
                                                      FStar_Tactics_InterpFuns.mktac1
                                                        "tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term
                                                       in
                                                    let uu____761 =
                                                      let uu____764 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          "unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                         in
                                                      let uu____765 =
                                                        let uu____768 =
                                                          FStar_Tactics_InterpFuns.mktac2
                                                            "unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_any
                                                           in
                                                        let uu____769 =
                                                          let uu____772 =
                                                            FStar_Tactics_InterpFuns.mktac1
                                                              "prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Syntax_Embeddings.e_unit
                                                             in
                                                          let uu____773 =
                                                            let uu____776 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                "addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____777 =
                                                              let uu____780 =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  "print"
                                                                  FStar_Tactics_Basic.print
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                 in
                                                              let uu____781 =
                                                                let uu____784
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mktac1
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                   in
                                                                let uu____785
                                                                  =
                                                                  let uu____788
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                  let uu____789
                                                                    =
                                                                    let uu____792
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____793
                                                                    =
                                                                    let uu____796
                                                                    =
                                                                    let uu____797
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____797
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____804
                                                                    =
                                                                    let uu____807
                                                                    =
                                                                    let uu____808
                                                                    =
                                                                    let uu____820
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____820
                                                                     in
                                                                    let uu____831
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____808
                                                                    uu____831
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____847
                                                                    =
                                                                    let uu____850
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____851
                                                                    =
                                                                    let uu____854
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____855
                                                                    =
                                                                    let uu____858
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____859
                                                                    =
                                                                    let uu____862
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____863
                                                                    =
                                                                    let uu____866
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____867
                                                                    =
                                                                    let uu____870
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____871
                                                                    =
                                                                    let uu____874
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____875
                                                                    =
                                                                    let uu____878
                                                                    =
                                                                    let uu____879
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____879
                                                                     in
                                                                    let uu____890
                                                                    =
                                                                    let uu____893
                                                                    =
                                                                    let uu____894
                                                                    =
                                                                    let uu____903
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_fv
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    uu____903
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "t_destruct"
                                                                    FStar_Tactics_Basic.t_destruct
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____894
                                                                     in
                                                                    let uu____920
                                                                    =
                                                                    let uu____923
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____924
                                                                    =
                                                                    let uu____927
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____928
                                                                    =
                                                                    let uu____931
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____932
                                                                    =
                                                                    let uu____935
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____936
                                                                    =
                                                                    let uu____939
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                     in
                                                                    let uu____940
                                                                    =
                                                                    let uu____943
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____944
                                                                    =
                                                                    let uu____947
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____948
                                                                    =
                                                                    let uu____951
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____952
                                                                    =
                                                                    let uu____955
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____956
                                                                    =
                                                                    let uu____959
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____960
                                                                    =
                                                                    let uu____963
                                                                    =
                                                                    let uu____964
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____964
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____971
                                                                    =
                                                                    let uu____974
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____975
                                                                    =
                                                                    let uu____978
                                                                    =
                                                                    let uu____979
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____979
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____986
                                                                    =
                                                                    let uu____989
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                     in
                                                                    let uu____990
                                                                    =
                                                                    let uu____993
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____994
                                                                    =
                                                                    let uu____997
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                     in
                                                                    let uu____998
                                                                    =
                                                                    let uu____1001
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____1002
                                                                    =
                                                                    let uu____1005
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    [uu____1005;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
                                                                     in
                                                                    uu____1001
                                                                    ::
                                                                    uu____1002
                                                                     in
                                                                    uu____997
                                                                    ::
                                                                    uu____998
                                                                     in
                                                                    uu____993
                                                                    ::
                                                                    uu____994
                                                                     in
                                                                    uu____989
                                                                    ::
                                                                    uu____990
                                                                     in
                                                                    uu____978
                                                                    ::
                                                                    uu____986
                                                                     in
                                                                    uu____974
                                                                    ::
                                                                    uu____975
                                                                     in
                                                                    uu____963
                                                                    ::
                                                                    uu____971
                                                                     in
                                                                    uu____959
                                                                    ::
                                                                    uu____960
                                                                     in
                                                                    uu____955
                                                                    ::
                                                                    uu____956
                                                                     in
                                                                    uu____951
                                                                    ::
                                                                    uu____952
                                                                     in
                                                                    uu____947
                                                                    ::
                                                                    uu____948
                                                                     in
                                                                    uu____943
                                                                    ::
                                                                    uu____944
                                                                     in
                                                                    uu____939
                                                                    ::
                                                                    uu____940
                                                                     in
                                                                    uu____935
                                                                    ::
                                                                    uu____936
                                                                     in
                                                                    uu____931
                                                                    ::
                                                                    uu____932
                                                                     in
                                                                    uu____927
                                                                    ::
                                                                    uu____928
                                                                     in
                                                                    uu____923
                                                                    ::
                                                                    uu____924
                                                                     in
                                                                    uu____893
                                                                    ::
                                                                    uu____920
                                                                     in
                                                                    uu____878
                                                                    ::
                                                                    uu____890
                                                                     in
                                                                    uu____874
                                                                    ::
                                                                    uu____875
                                                                     in
                                                                    uu____870
                                                                    ::
                                                                    uu____871
                                                                     in
                                                                    uu____866
                                                                    ::
                                                                    uu____867
                                                                     in
                                                                    uu____862
                                                                    ::
                                                                    uu____863
                                                                     in
                                                                    uu____858
                                                                    ::
                                                                    uu____859
                                                                     in
                                                                    uu____854
                                                                    ::
                                                                    uu____855
                                                                     in
                                                                    uu____850
                                                                    ::
                                                                    uu____851
                                                                     in
                                                                    uu____807
                                                                    ::
                                                                    uu____847
                                                                     in
                                                                    uu____796
                                                                    ::
                                                                    uu____804
                                                                     in
                                                                    uu____792
                                                                    ::
                                                                    uu____793
                                                                     in
                                                                  uu____788
                                                                    ::
                                                                    uu____789
                                                                   in
                                                                uu____784 ::
                                                                  uu____785
                                                                 in
                                                              uu____780 ::
                                                                uu____781
                                                               in
                                                            uu____776 ::
                                                              uu____777
                                                             in
                                                          uu____772 ::
                                                            uu____773
                                                           in
                                                        uu____768 ::
                                                          uu____769
                                                         in
                                                      uu____764 :: uu____765
                                                       in
                                                    uu____760 :: uu____761
                                                     in
                                                  uu____756 :: uu____757  in
                                                uu____738 :: uu____753  in
                                              uu____705 :: uu____735  in
                                            uu____701 :: uu____702  in
                                          uu____697 :: uu____698  in
                                        uu____693 :: uu____694  in
                                      uu____689 :: uu____690  in
                                    uu____685 :: uu____686  in
                                  uu____681 :: uu____682  in
                                uu____677 :: uu____678  in
                              uu____673 :: uu____674  in
                            uu____669 :: uu____670  in
                          uu____665 :: uu____666  in
                        uu____661 :: uu____662  in
                      uu____657 :: uu____658  in
                    uu____646 :: uu____654  in
                  uu____635 :: uu____643  in
                uu____624 :: uu____632  in
              uu____609 :: uu____621  in
            uu____605 :: uu____606  in
          uu____585 :: uu____602  in
        uu____581 :: uu____582  in
      uu____575 :: uu____578  in
    FStar_List.append uu____572
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
             let app =
               let uu____1028 =
                 let uu____1033 =
                   let uu____1034 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____1034]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____1033  in
               uu____1028 FStar_Pervasives_Native.None rng  in
             unembed_tactic_0 er app)

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
             let uu____1082 =
               let uu____1087 =
                 let uu____1088 =
                   let uu____1097 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____1097  in
                 [uu____1088]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1087  in
             uu____1082 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Env.Weak;
             FStar_TypeChecker_Env.Reify;
             FStar_TypeChecker_Env.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Env.UnfoldTac;
             FStar_TypeChecker_Env.Primops;
             FStar_TypeChecker_Env.Unascribe]  in
           let steps1 =
             let uu____1120 = FStar_Options.tactics_nbe ()  in
             if uu____1120 then FStar_TypeChecker_Env.NBE :: steps else steps
              in
           if proof_state.FStar_Tactics_Types.tac_verb_dbg
           then
             (let uu____1123 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1123)
           else ();
           (let result =
              let uu____1126 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1126 steps1
                proof_state.FStar_Tactics_Types.main_context tm
               in
            if proof_state.FStar_Tactics_Types.tac_verb_dbg
            then
              (let uu____1130 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____1130)
            else ();
            (let res =
               let uu____1137 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____1137 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1150 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1150
                   (fun uu____1154  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1159 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1159
                   (fun uu____1163  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1166 =
                   let uu____1171 =
                     let uu____1172 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1172
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1171)  in
                 FStar_Errors.raise_error uu____1166
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____1179 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
        uu____1179

let report_implicits :
  'Auu____1196 . 'Auu____1196 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1225 =
               let uu____1226 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1227 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1226 uu____1227 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1225, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____1266 = FStar_ST.op_Bang tacdbg  in
             if uu____1266
             then
               let uu____1286 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1286
             else ());
            (let uu____1288 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1288 with
             | (uu____1301,uu____1302,g) ->
                 ((let uu____1305 = FStar_ST.op_Bang tacdbg  in
                   if uu____1305 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                      in
                   let uu____1331 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1331 with
                   | (env1,uu____1345) ->
                       let env2 =
                         let uu___344_1351 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___344_1351.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___344_1351.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___344_1351.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___344_1351.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___344_1351.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___344_1351.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___344_1351.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___344_1351.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___344_1351.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___344_1351.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___344_1351.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___344_1351.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___344_1351.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___344_1351.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___344_1351.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___344_1351.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___344_1351.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___344_1351.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___344_1351.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___344_1351.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___344_1351.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___344_1351.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___344_1351.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___344_1351.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___344_1351.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___344_1351.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___344_1351.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___344_1351.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___344_1351.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___344_1351.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___344_1351.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___344_1351.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___344_1351.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___344_1351.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___344_1351.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___344_1351.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___344_1351.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___344_1351.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___344_1351.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___344_1351.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___344_1351.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env3 =
                         let uu___345_1353 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___345_1353.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___345_1353.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___345_1353.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___345_1353.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___345_1353.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___345_1353.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___345_1353.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___345_1353.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___345_1353.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___345_1353.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___345_1353.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___345_1353.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___345_1353.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___345_1353.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___345_1353.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___345_1353.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___345_1353.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___345_1353.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___345_1353.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___345_1353.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___345_1353.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___345_1353.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___345_1353.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___345_1353.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___345_1353.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___345_1353.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___345_1353.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___345_1353.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___345_1353.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___345_1353.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___345_1353.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___345_1353.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___345_1353.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___345_1353.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___345_1353.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___345_1353.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___345_1353.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___345_1353.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___345_1353.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___345_1353.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___345_1353.FStar_TypeChecker_Env.nbe)
                         }  in
                       let env4 =
                         let uu___346_1355 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___346_1355.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___346_1355.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___346_1355.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___346_1355.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___346_1355.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___346_1355.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___346_1355.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___346_1355.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___346_1355.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___346_1355.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___346_1355.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___346_1355.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___346_1355.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___346_1355.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___346_1355.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___346_1355.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___346_1355.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___346_1355.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___346_1355.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___346_1355.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___346_1355.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___346_1355.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___346_1355.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___346_1355.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___346_1355.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___346_1355.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___346_1355.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___346_1355.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___346_1355.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___346_1355.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___346_1355.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___346_1355.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___346_1355.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___346_1355.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___346_1355.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___346_1355.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___346_1355.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___346_1355.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___346_1355.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___346_1355.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___346_1355.FStar_TypeChecker_Env.nbe)
                         }  in
                       let rng =
                         let uu____1357 = FStar_Range.use_range rng_goal  in
                         let uu____1358 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1357 uu____1358  in
                       let uu____1359 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1359 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1397 = FStar_ST.op_Bang tacdbg  in
                              if uu____1397
                              then
                                let uu____1417 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____1417
                              else ());
                             (let uu____1419 =
                                FStar_Util.record_time
                                  (fun uu____1429  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____1419 with
                              | (res,ms) ->
                                  ((let uu____1443 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____1443
                                    then
                                      let uu____1463 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____1464 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____1465 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____1463 uu____1464 uu____1465
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____1473,ps1) ->
                                        ((let uu____1476 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1476
                                          then
                                            let uu____1496 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____1496
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____1503 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____1503
                                              then
                                                let uu____1504 =
                                                  let uu____1505 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____1506 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____1505 uu____1506
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____1504
                                                 then ()
                                                 else
                                                   (let uu____1508 =
                                                      let uu____1509 =
                                                        let uu____1510 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____1510
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____1509
                                                       in
                                                    failwith uu____1508))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____1513 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1513
                                          then
                                            let uu____1533 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____1533
                                          else ());
                                         (let g1 =
                                            let uu___347_1538 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___347_1538.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___347_1538.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___347_1538.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____1541 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____1541
                                           then
                                             let uu____1561 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print1
                                               "Checked (1) implicits: %s\n"
                                               uu____1561
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____1567 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1567
                                            then
                                              let uu____1587 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "Checked (2) implicits: %s\n"
                                                uu____1587
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____1597 =
                                            let uu____1598 =
                                              FStar_TypeChecker_Cfg.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____1598 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____1597
                                            "at the time of failure");
                                         (let uu____1599 =
                                            let uu____1604 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____1604)
                                             in
                                          FStar_Errors.raise_error uu____1599
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____1616 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____1622 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____1628 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____1683 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____1723 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____1777 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____1818 . 'Auu____1818 -> 'Auu____1818 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1846 = FStar_Syntax_Util.head_and_args t  in
        match uu____1846 with
        | (hd1,args) ->
            let uu____1889 =
              let uu____1904 =
                let uu____1905 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1905.FStar_Syntax_Syntax.n  in
              (uu____1904, args)  in
            (match uu____1889 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1920))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____1983 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1983 with
                       | (gs,uu____1991) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____1998 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1998 with
                       | (gs,uu____2006) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2049 =
                        let uu____2056 =
                          let uu____2059 =
                            let uu____2060 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2060
                             in
                          [uu____2059]  in
                        (FStar_Syntax_Util.t_true, uu____2056)  in
                      Simplified uu____2049
                  | Both  ->
                      let uu____2071 =
                        let uu____2080 =
                          let uu____2083 =
                            let uu____2084 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2084
                             in
                          [uu____2083]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2080)  in
                      Dual uu____2071
                  | Neg  -> Simplified (assertion, []))
             | uu____2097 -> Unchanged t)
  
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
    fun uu___343_2187  ->
      match uu___343_2187 with
      | Unchanged t -> let uu____2193 = f t  in Unchanged uu____2193
      | Simplified (t,gs) ->
          let uu____2200 = let uu____2207 = f t  in (uu____2207, gs)  in
          Simplified uu____2200
      | Dual (tn,tp,gs) ->
          let uu____2217 =
            let uu____2226 = f tn  in
            let uu____2227 = f tp  in (uu____2226, uu____2227, gs)  in
          Dual uu____2217
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2290 = f t1 t2  in Unchanged uu____2290
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2302 = let uu____2309 = f t1 t2  in (uu____2309, gs)
               in
            Simplified uu____2302
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2323 = let uu____2330 = f t1 t2  in (uu____2330, gs)
               in
            Simplified uu____2323
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2349 =
              let uu____2356 = f t1 t2  in
              (uu____2356, (FStar_List.append gs1 gs2))  in
            Simplified uu____2349
        | uu____2359 ->
            let uu____2368 = explode x  in
            (match uu____2368 with
             | (n1,p1,gs1) ->
                 let uu____2386 = explode y  in
                 (match uu____2386 with
                  | (n2,p2,gs2) ->
                      let uu____2404 =
                        let uu____2413 = f n1 n2  in
                        let uu____2414 = f p1 p2  in
                        (uu____2413, uu____2414, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____2404))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____2486 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____2486
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____2534  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____2576 =
              let uu____2577 = FStar_Syntax_Subst.compress t  in
              uu____2577.FStar_Syntax_Syntax.n  in
            match uu____2576 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____2589 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____2589 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____2615 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____2615 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2635;
                   FStar_Syntax_Syntax.vars = uu____2636;_},(p,uu____2638)::
                 (q,uu____2640)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2696 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2696
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____2699 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____2699 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____2713 = FStar_Syntax_Util.mk_imp l r  in
                       uu____2713.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2717;
                   FStar_Syntax_Syntax.vars = uu____2718;_},(p,uu____2720)::
                 (q,uu____2722)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____2778 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2778
                   in
                let xq =
                  let uu____2780 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2780
                   in
                let r1 =
                  let uu____2782 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____2782 p  in
                let r2 =
                  let uu____2784 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____2784 q  in
                (match (r1, r2) with
                 | (Unchanged uu____2791,Unchanged uu____2792) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____2810 = FStar_Syntax_Util.mk_iff l r  in
                            uu____2810.FStar_Syntax_Syntax.n) r1 r2
                 | uu____2813 ->
                     let uu____2822 = explode r1  in
                     (match uu____2822 with
                      | (pn,pp,gs1) ->
                          let uu____2840 = explode r2  in
                          (match uu____2840 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____2861 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____2864 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____2861
                                   uu____2864
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____2928  ->
                       fun r  ->
                         match uu____2928 with
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
                let uu____3080 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3080 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3120  ->
                            match uu____3120 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3142 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___348_3174 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___348_3174.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___348_3174.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3142 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3202 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3202.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3248 = traverse f pol e t1  in
                let uu____3253 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3253 uu____3248
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___349_3293 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___349_3293.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___349_3293.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3300 =
                f pol e
                  (let uu___350_3304 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___350_3304.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___350_3304.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3300
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___351_3314 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___351_3314.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___351_3314.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3315 = explode rp  in
              (match uu____3315 with
               | (uu____3324,p',gs') ->
                   Dual
                     ((let uu___352_3334 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___352_3334.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___352_3334.FStar_Syntax_Syntax.vars)
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
      (let uu____3377 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____3377);
      (let uu____3398 = FStar_ST.op_Bang tacdbg  in
       if uu____3398
       then
         let uu____3418 =
           let uu____3419 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____3419
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____3420 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3418
           uu____3420
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____3449 =
         let uu____3458 = traverse by_tactic_interp Pos env goal  in
         match uu____3458 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____3482 -> failwith "no"  in
       match uu____3449 with
       | (t',gs) ->
           ((let uu____3510 = FStar_ST.op_Bang tacdbg  in
             if uu____3510
             then
               let uu____3530 =
                 let uu____3531 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____3531
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____3532 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3530 uu____3532
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3580  ->
                    fun g  ->
                      match uu____3580 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3625 =
                              let uu____3628 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____3629 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____3628 uu____3629  in
                            match uu____3625 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3630 =
                                  let uu____3635 =
                                    let uu____3636 =
                                      let uu____3637 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____3637
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____3636
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____3635)
                                   in
                                FStar_Errors.raise_error uu____3630
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____3640 = FStar_ST.op_Bang tacdbg  in
                            if uu____3640
                            then
                              let uu____3660 = FStar_Util.string_of_int n1
                                 in
                              let uu____3661 =
                                let uu____3662 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____3662
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3660 uu____3661
                            else ());
                           (let gt' =
                              let uu____3665 =
                                let uu____3666 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____3666
                                 in
                              FStar_TypeChecker_Util.label uu____3665
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____3667 =
                              let uu____3676 =
                                let uu____3683 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____3683, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____3676 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____3667)))) s
                 gs
                in
             let uu____3698 = s1  in
             match uu____3698 with
             | (uu____3719,gs1) ->
                 let uu____3737 =
                   let uu____3744 = FStar_Options.peek ()  in
                   (env, t', uu____3744)  in
                 uu____3737 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____3757 =
        let uu____3758 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____3758  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3757 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____3759 =
      let uu____3764 =
        let uu____3765 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____3774 =
          let uu____3785 = FStar_Syntax_Syntax.as_arg a  in [uu____3785]  in
        uu____3765 :: uu____3774  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3764  in
    uu____3759 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____3835 =
            let uu____3840 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____3841 =
              let uu____3842 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3842]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____3840 uu____3841  in
          uu____3835 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____3871 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____3871);
           (let uu____3891 =
              let uu____3898 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____3898 env typ
               in
            match uu____3891 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____3912 =
                        let uu____3915 = FStar_Tactics_Types.goal_env g  in
                        let uu____3916 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____3915 uu____3916  in
                      match uu____3912 with
                      | FStar_Pervasives_Native.Some vc ->
                          let guard =
                            {
                              FStar_TypeChecker_Env.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Env.deferred = [];
                              FStar_TypeChecker_Env.univ_ineqs = ([], []);
                              FStar_TypeChecker_Env.implicits = []
                            }  in
                          let uu____3927 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____3927 guard
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
        ((let uu____3944 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____3944);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____3965 =
            let uu____3972 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____3972 env typ
             in
          match uu____3965 with
          | (gs,w) ->
              ((let uu____3982 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____3986 =
                         let uu____3987 =
                           let uu____3990 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____3991 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____3990 uu____3991  in
                         FStar_Option.isSome uu____3987  in
                       Prims.op_Negation uu____3986) gs
                   in
                if uu____3982
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
                (let uu____3995 = FStar_ST.op_Bang tacdbg  in
                 if uu____3995
                 then
                   let uu____4015 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____4015
                 else ());
                (let uu____4017 =
                   let uu____4022 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Syntax_Embeddings.unembed uu____4022 w1  in
                 match uu____4017 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  