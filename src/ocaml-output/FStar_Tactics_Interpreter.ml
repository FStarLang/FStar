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
  unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list) =
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
                 let uu____242 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____243 = FStar_Tactics_Types.decr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____242 uu____243
                  in
               FStar_Pervasives_Native.Some uu____241)
      | uu____244 -> failwith "Unexpected application of decr_depth"  in
    let decr_depth_step =
      let uu____248 = FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth"
         in
      {
        FStar_TypeChecker_Normalize.name = uu____248;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      }  in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____265)::[] ->
          let uu____290 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____290
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               let uu____298 =
                 let uu____299 = FStar_TypeChecker_Normalize.psc_range psc
                    in
                 let uu____300 = FStar_Tactics_Types.incr_depth ps2  in
                 FStar_Syntax_Embeddings.embed
                   FStar_Tactics_Embedding.e_proofstate uu____299 uu____300
                  in
               FStar_Pervasives_Native.Some uu____298)
      | uu____301 -> failwith "Unexpected application of incr_depth"  in
    let incr_depth_step =
      let uu____305 = FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth"
         in
      {
        FStar_TypeChecker_Normalize.name = uu____305;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      }  in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____322)::[] ->
          let uu____347 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____347
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1  in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____356 -> failwith "Unexpected application of tracepoint"  in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____375)::(r,uu____377)::[] ->
          let uu____418 =
            FStar_Syntax_Embeddings.unembed
              FStar_Tactics_Embedding.e_proofstate ps
             in
          FStar_Util.bind_opt uu____418
            (fun ps1  ->
               let uu____424 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Syntax_Embeddings.e_range r
                  in
               FStar_Util.bind_opt uu____424
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1
                       in
                    let uu____432 =
                      let uu____433 =
                        FStar_TypeChecker_Normalize.psc_range psc  in
                      FStar_Syntax_Embeddings.embed
                        FStar_Tactics_Embedding.e_proofstate uu____433 ps'
                       in
                    FStar_Pervasives_Native.Some uu____432))
      | uu____434 ->
          failwith "Unexpected application of set_proofstate_range"
       in
    let push_binder_interp psc args =
      match args with
      | (env_t,uu____453)::(b,uu____455)::[] ->
          let uu____496 =
            FStar_Syntax_Embeddings.unembed FStar_Reflection_Embeddings.e_env
              env_t
             in
          FStar_Util.bind_opt uu____496
            (fun env  ->
               let uu____502 =
                 FStar_Syntax_Embeddings.unembed
                   FStar_Reflection_Embeddings.e_binder b
                  in
               FStar_Util.bind_opt uu____502
                 (fun b1  ->
                    let env1 = FStar_TypeChecker_Env.push_binders env [b1]
                       in
                    let uu____522 =
                      FStar_Syntax_Embeddings.embed
                        FStar_Reflection_Embeddings.e_env
                        env_t.FStar_Syntax_Syntax.pos env1
                       in
                    FStar_Pervasives_Native.Some uu____522))
      | uu____523 -> failwith "Unexpected application of push_binder"  in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          set_proofstate_range_interp
      }  in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint"  in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      }  in
    let push_binder_step =
      let nm =
        FStar_Tactics_Embedding.fstar_tactics_lid'
          ["Builtins"; "push_binder"]
         in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.auto_reflect =
          FStar_Pervasives_Native.None;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = push_binder_interp
      }  in
    let uu____532 =
      let uu____535 =
        FStar_Tactics_InterpFuns.mktac2 "fail"
          (fun uu____537  -> FStar_Tactics_Basic.fail)
          FStar_Syntax_Embeddings.e_any FStar_Syntax_Embeddings.e_string
          FStar_Syntax_Embeddings.e_any
         in
      let uu____538 =
        let uu____541 =
          FStar_Tactics_InterpFuns.mktac1 "trivial"
            FStar_Tactics_Basic.trivial FStar_Syntax_Embeddings.e_unit
            FStar_Syntax_Embeddings.e_unit
           in
        let uu____542 =
          let uu____545 =
            let uu____546 = e_tactic_0' FStar_Syntax_Embeddings.e_any  in
            let uu____551 =
              FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_any
               in
            FStar_Tactics_InterpFuns.mktac2 "__trytac"
              (fun uu____561  -> FStar_Tactics_Basic.trytac)
              FStar_Syntax_Embeddings.e_any uu____546 uu____551
             in
          let uu____562 =
            let uu____565 =
              FStar_Tactics_InterpFuns.mktac1 "intro"
                FStar_Tactics_Basic.intro FStar_Syntax_Embeddings.e_unit
                FStar_Reflection_Embeddings.e_binder
               in
            let uu____566 =
              let uu____569 =
                let uu____570 =
                  FStar_Syntax_Embeddings.e_tuple2
                    FStar_Reflection_Embeddings.e_binder
                    FStar_Reflection_Embeddings.e_binder
                   in
                FStar_Tactics_InterpFuns.mktac1 "intro_rec"
                  FStar_Tactics_Basic.intro_rec
                  FStar_Syntax_Embeddings.e_unit uu____570
                 in
              let uu____581 =
                let uu____584 =
                  let uu____585 =
                    FStar_Syntax_Embeddings.e_list
                      FStar_Syntax_Embeddings.e_norm_step
                     in
                  FStar_Tactics_InterpFuns.mktac1 "norm"
                    FStar_Tactics_Basic.norm uu____585
                    FStar_Syntax_Embeddings.e_unit
                   in
                let uu____592 =
                  let uu____595 =
                    let uu____596 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_norm_step
                       in
                    FStar_Tactics_InterpFuns.mktac3 "norm_term_env"
                      FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Embeddings.e_env uu____596
                      FStar_Reflection_Embeddings.e_term
                      FStar_Reflection_Embeddings.e_term
                     in
                  let uu____603 =
                    let uu____606 =
                      let uu____607 =
                        FStar_Syntax_Embeddings.e_list
                          FStar_Syntax_Embeddings.e_norm_step
                         in
                      FStar_Tactics_InterpFuns.mktac2 "norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____607
                        FStar_Reflection_Embeddings.e_binder
                        FStar_Syntax_Embeddings.e_unit
                       in
                    let uu____614 =
                      let uu____617 =
                        FStar_Tactics_InterpFuns.mktac2 "rename_to"
                          FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Embeddings.e_binder
                          FStar_Syntax_Embeddings.e_string
                          FStar_Syntax_Embeddings.e_unit
                         in
                      let uu____618 =
                        let uu____621 =
                          FStar_Tactics_InterpFuns.mktac1 "binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Embeddings.e_binder
                            FStar_Syntax_Embeddings.e_unit
                           in
                        let uu____622 =
                          let uu____625 =
                            FStar_Tactics_InterpFuns.mktac1 "revert"
                              FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.e_unit
                              FStar_Syntax_Embeddings.e_unit
                             in
                          let uu____626 =
                            let uu____629 =
                              FStar_Tactics_InterpFuns.mktac1 "clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.e_unit
                                FStar_Syntax_Embeddings.e_unit
                               in
                            let uu____630 =
                              let uu____633 =
                                FStar_Tactics_InterpFuns.mktac1 "clear"
                                  FStar_Tactics_Basic.clear
                                  FStar_Reflection_Embeddings.e_binder
                                  FStar_Syntax_Embeddings.e_unit
                                 in
                              let uu____634 =
                                let uu____637 =
                                  FStar_Tactics_InterpFuns.mktac1 "rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Embeddings.e_binder
                                    FStar_Syntax_Embeddings.e_unit
                                   in
                                let uu____638 =
                                  let uu____641 =
                                    FStar_Tactics_InterpFuns.mktac1 "smt"
                                      FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.e_unit
                                      FStar_Syntax_Embeddings.e_unit
                                     in
                                  let uu____642 =
                                    let uu____645 =
                                      FStar_Tactics_InterpFuns.mktac1
                                        "refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.e_unit
                                        FStar_Syntax_Embeddings.e_unit
                                       in
                                    let uu____646 =
                                      let uu____649 =
                                        FStar_Tactics_InterpFuns.mktac2
                                          "t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.e_bool
                                          FStar_Reflection_Embeddings.e_term
                                          FStar_Syntax_Embeddings.e_unit
                                         in
                                      let uu____650 =
                                        let uu____653 =
                                          FStar_Tactics_InterpFuns.mktac1
                                            "apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Embeddings.e_term
                                            FStar_Syntax_Embeddings.e_unit
                                           in
                                        let uu____654 =
                                          let uu____657 =
                                            FStar_Tactics_InterpFuns.mktac1
                                              "apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Embeddings.e_term
                                              FStar_Syntax_Embeddings.e_unit
                                             in
                                          let uu____658 =
                                            let uu____661 =
                                              FStar_Tactics_InterpFuns.mktac1
                                                "apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Embeddings.e_term
                                                FStar_Syntax_Embeddings.e_unit
                                               in
                                            let uu____662 =
                                              let uu____665 =
                                                let uu____666 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____671 =
                                                  e_tactic_0'
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                let uu____676 =
                                                  FStar_Syntax_Embeddings.e_tuple2
                                                    FStar_Syntax_Embeddings.e_any
                                                    FStar_Syntax_Embeddings.e_any
                                                   in
                                                FStar_Tactics_InterpFuns.mktac5
                                                  "__divide"
                                                  (fun uu____693  ->
                                                     fun uu____694  ->
                                                       FStar_Tactics_Basic.divide)
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_any
                                                  FStar_Syntax_Embeddings.e_int
                                                  uu____666 uu____671
                                                  uu____676
                                                 in
                                              let uu____695 =
                                                let uu____698 =
                                                  let uu____699 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____704 =
                                                    e_tactic_0'
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  FStar_Tactics_InterpFuns.mktac2
                                                    "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    uu____699 uu____704
                                                    FStar_Syntax_Embeddings.e_unit
                                                   in
                                                let uu____713 =
                                                  let uu____716 =
                                                    FStar_Tactics_InterpFuns.mktac1
                                                      "set_options"
                                                      FStar_Tactics_Basic.set_options
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_Syntax_Embeddings.e_unit
                                                     in
                                                  let uu____717 =
                                                    let uu____720 =
                                                      FStar_Tactics_InterpFuns.mktac1
                                                        "tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Embeddings.e_term
                                                        FStar_Reflection_Embeddings.e_term
                                                       in
                                                    let uu____721 =
                                                      let uu____724 =
                                                        FStar_Tactics_InterpFuns.mktac1
                                                          "unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Embeddings.e_term
                                                          FStar_Syntax_Embeddings.e_unit
                                                         in
                                                      let uu____725 =
                                                        let uu____728 =
                                                          FStar_Tactics_InterpFuns.mktac2
                                                            "unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            FStar_Syntax_Embeddings.e_any
                                                            FStar_Reflection_Embeddings.e_term
                                                            FStar_Syntax_Embeddings.e_any
                                                           in
                                                        let uu____729 =
                                                          let uu____732 =
                                                            FStar_Tactics_InterpFuns.mktac1
                                                              "prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.e_string
                                                              FStar_Syntax_Embeddings.e_unit
                                                             in
                                                          let uu____733 =
                                                            let uu____736 =
                                                              FStar_Tactics_InterpFuns.mktac1
                                                                "addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.e_string
                                                                FStar_Syntax_Embeddings.e_unit
                                                               in
                                                            let uu____737 =
                                                              let uu____740 =
                                                                FStar_Tactics_InterpFuns.mktac1
                                                                  "print"
                                                                  FStar_Tactics_Basic.print
                                                                  FStar_Syntax_Embeddings.e_string
                                                                  FStar_Syntax_Embeddings.e_unit
                                                                 in
                                                              let uu____741 =
                                                                let uu____744
                                                                  =
                                                                  FStar_Tactics_InterpFuns.mktac1
                                                                    "debug"
                                                                    FStar_Tactics_Basic.debug
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                   in
                                                                let uu____745
                                                                  =
                                                                  let uu____748
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                  let uu____749
                                                                    =
                                                                    let uu____752
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____753
                                                                    =
                                                                    let uu____756
                                                                    =
                                                                    let uu____757
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.e_direction
                                                                    uu____757
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____764
                                                                    =
                                                                    let uu____767
                                                                    =
                                                                    let uu____768
                                                                    =
                                                                    let uu____780
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    e_tactic_1
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____780
                                                                     in
                                                                    let uu____791
                                                                    =
                                                                    e_tactic_0'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "__topdown_rewrite"
                                                                    FStar_Tactics_Basic.topdown_rewrite
                                                                    uu____768
                                                                    uu____791
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____807
                                                                    =
                                                                    let uu____810
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____811
                                                                    =
                                                                    let uu____814
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____815
                                                                    =
                                                                    let uu____818
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____819
                                                                    =
                                                                    let uu____822
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____823
                                                                    =
                                                                    let uu____826
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____827
                                                                    =
                                                                    let uu____830
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "dismiss"
                                                                    FStar_Tactics_Basic.dismiss
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____831
                                                                    =
                                                                    let uu____834
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "tadmit"
                                                                    FStar_Tactics_Basic.tadmit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____835
                                                                    =
                                                                    let uu____838
                                                                    =
                                                                    let uu____839
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_tuple2
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    uu____839
                                                                     in
                                                                    let uu____850
                                                                    =
                                                                    let uu____853
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____854
                                                                    =
                                                                    let uu____857
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_env
                                                                     in
                                                                    let uu____858
                                                                    =
                                                                    let uu____861
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____862
                                                                    =
                                                                    let uu____865
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____866
                                                                    =
                                                                    let uu____869
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "inspect"
                                                                    FStar_Tactics_Basic.inspect
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                     in
                                                                    let uu____870
                                                                    =
                                                                    let uu____873
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "pack"
                                                                    FStar_Tactics_Basic.pack
                                                                    FStar_Reflection_Embeddings.e_term_view
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____874
                                                                    =
                                                                    let uu____877
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "fresh"
                                                                    FStar_Tactics_Basic.fresh
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____878
                                                                    =
                                                                    let uu____881
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "ngoals"
                                                                    FStar_Tactics_Basic.ngoals
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____882
                                                                    =
                                                                    let uu____885
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "ngoals_smt"
                                                                    FStar_Tactics_Basic.ngoals_smt
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_int
                                                                     in
                                                                    let uu____886
                                                                    =
                                                                    let uu____889
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____890
                                                                    =
                                                                    let uu____893
                                                                    =
                                                                    let uu____894
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_option
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    uu____894
                                                                    FStar_Reflection_Embeddings.e_term
                                                                     in
                                                                    let uu____901
                                                                    =
                                                                    let uu____904
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    "unify_env"
                                                                    FStar_Tactics_Basic.unify_env
                                                                    FStar_Reflection_Embeddings.e_env
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    let uu____905
                                                                    =
                                                                    let uu____908
                                                                    =
                                                                    let uu____909
                                                                    =
                                                                    FStar_Syntax_Embeddings.e_list
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    FStar_Tactics_InterpFuns.mktac3
                                                                    "launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    uu____909
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Syntax_Embeddings.e_string
                                                                     in
                                                                    let uu____916
                                                                    =
                                                                    let uu____919
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac2
                                                                    "fresh_bv_named"
                                                                    FStar_Tactics_Basic.fresh_bv_named
                                                                    FStar_Syntax_Embeddings.e_string
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Reflection_Embeddings.e_bv
                                                                     in
                                                                    let uu____920
                                                                    =
                                                                    let uu____923
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "change"
                                                                    FStar_Tactics_Basic.change
                                                                    FStar_Reflection_Embeddings.e_term
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____924
                                                                    =
                                                                    let uu____927
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "get_guard_policy"
                                                                    FStar_Tactics_Basic.get_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                     in
                                                                    let uu____928
                                                                    =
                                                                    let uu____931
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "set_guard_policy"
                                                                    FStar_Tactics_Basic.set_guard_policy
                                                                    FStar_Tactics_Embedding.e_guard_policy
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                     in
                                                                    let uu____932
                                                                    =
                                                                    let uu____935
                                                                    =
                                                                    FStar_Tactics_InterpFuns.mktac1
                                                                    "lax_on"
                                                                    FStar_Tactics_Basic.lax_on
                                                                    FStar_Syntax_Embeddings.e_unit
                                                                    FStar_Syntax_Embeddings.e_bool
                                                                     in
                                                                    [uu____935;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step;
                                                                    push_binder_step]
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
                                                                    uu____919
                                                                    ::
                                                                    uu____920
                                                                     in
                                                                    uu____908
                                                                    ::
                                                                    uu____916
                                                                     in
                                                                    uu____904
                                                                    ::
                                                                    uu____905
                                                                     in
                                                                    uu____893
                                                                    ::
                                                                    uu____901
                                                                     in
                                                                    uu____889
                                                                    ::
                                                                    uu____890
                                                                     in
                                                                    uu____885
                                                                    ::
                                                                    uu____886
                                                                     in
                                                                    uu____881
                                                                    ::
                                                                    uu____882
                                                                     in
                                                                    uu____877
                                                                    ::
                                                                    uu____878
                                                                     in
                                                                    uu____873
                                                                    ::
                                                                    uu____874
                                                                     in
                                                                    uu____869
                                                                    ::
                                                                    uu____870
                                                                     in
                                                                    uu____865
                                                                    ::
                                                                    uu____866
                                                                     in
                                                                    uu____861
                                                                    ::
                                                                    uu____862
                                                                     in
                                                                    uu____857
                                                                    ::
                                                                    uu____858
                                                                     in
                                                                    uu____853
                                                                    ::
                                                                    uu____854
                                                                     in
                                                                    uu____838
                                                                    ::
                                                                    uu____850
                                                                     in
                                                                    uu____834
                                                                    ::
                                                                    uu____835
                                                                     in
                                                                    uu____830
                                                                    ::
                                                                    uu____831
                                                                     in
                                                                    uu____826
                                                                    ::
                                                                    uu____827
                                                                     in
                                                                    uu____822
                                                                    ::
                                                                    uu____823
                                                                     in
                                                                    uu____818
                                                                    ::
                                                                    uu____819
                                                                     in
                                                                    uu____814
                                                                    ::
                                                                    uu____815
                                                                     in
                                                                    uu____810
                                                                    ::
                                                                    uu____811
                                                                     in
                                                                    uu____767
                                                                    ::
                                                                    uu____807
                                                                     in
                                                                    uu____756
                                                                    ::
                                                                    uu____764
                                                                     in
                                                                    uu____752
                                                                    ::
                                                                    uu____753
                                                                     in
                                                                  uu____748
                                                                    ::
                                                                    uu____749
                                                                   in
                                                                uu____744 ::
                                                                  uu____745
                                                                 in
                                                              uu____740 ::
                                                                uu____741
                                                               in
                                                            uu____736 ::
                                                              uu____737
                                                             in
                                                          uu____732 ::
                                                            uu____733
                                                           in
                                                        uu____728 ::
                                                          uu____729
                                                         in
                                                      uu____724 :: uu____725
                                                       in
                                                    uu____720 :: uu____721
                                                     in
                                                  uu____716 :: uu____717  in
                                                uu____698 :: uu____713  in
                                              uu____665 :: uu____695  in
                                            uu____661 :: uu____662  in
                                          uu____657 :: uu____658  in
                                        uu____653 :: uu____654  in
                                      uu____649 :: uu____650  in
                                    uu____645 :: uu____646  in
                                  uu____641 :: uu____642  in
                                uu____637 :: uu____638  in
                              uu____633 :: uu____634  in
                            uu____629 :: uu____630  in
                          uu____625 :: uu____626  in
                        uu____621 :: uu____622  in
                      uu____617 :: uu____618  in
                    uu____606 :: uu____614  in
                  uu____595 :: uu____603  in
                uu____584 :: uu____592  in
              uu____569 :: uu____581  in
            uu____565 :: uu____566  in
          uu____545 :: uu____562  in
        uu____541 :: uu____542  in
      uu____535 :: uu____538  in
    FStar_List.append uu____532
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
               let uu____958 =
                 let uu____963 =
                   let uu____964 = FStar_Syntax_Syntax.as_arg x_tm  in
                   [uu____964]  in
                 FStar_Syntax_Syntax.mk_Tm_app f uu____963  in
               uu____958 FStar_Pervasives_Native.None rng  in
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
             let uu____1011 =
               let uu____1016 =
                 let uu____1017 =
                   let uu____1026 =
                     FStar_Syntax_Embeddings.embed
                       FStar_Tactics_Embedding.e_proofstate rng proof_state
                      in
                   FStar_Syntax_Syntax.as_arg uu____1026  in
                 [uu____1017]  in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1016  in
             uu____1011 FStar_Pervasives_Native.None rng  in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops;
             FStar_TypeChecker_Normalize.Unascribe]  in
           if proof_state.FStar_Tactics_Types.tac_verb_dbg
           then
             (let uu____1049 = FStar_Syntax_Print.term_to_string tm  in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____1049)
           else ();
           (let result =
              let uu____1052 = primitive_steps ()  in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____1052 steps proof_state.FStar_Tactics_Types.main_context
                tm
               in
            if proof_state.FStar_Tactics_Types.tac_verb_dbg
            then
              (let uu____1056 = FStar_Syntax_Print.term_to_string result  in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____1056)
            else ();
            (let res =
               let uu____1063 = FStar_Tactics_Embedding.e_result eb  in
               FStar_Syntax_Embeddings.unembed uu____1063 result  in
             match res with
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Success
                 (b,ps)) ->
                 let uu____1076 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1076
                   (fun uu____1080  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Tactics_Result.Failed
                 (msg,ps)) ->
                 let uu____1085 = FStar_Tactics_Basic.set ps  in
                 FStar_Tactics_Basic.bind uu____1085
                   (fun uu____1089  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____1092 =
                   let uu____1097 =
                     let uu____1098 =
                       FStar_Syntax_Print.term_to_string result  in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____1098
                      in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____1097)  in
                 FStar_Errors.raise_error uu____1092
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))

and unembed_tactic_0' :
  'Ab .
    'Ab FStar_Syntax_Embeddings.embedding ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun eb  ->
    fun embedded_tac_b  ->
      let uu____1105 = unembed_tactic_0 eb embedded_tac_b  in
      FStar_All.pipe_left (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
        uu____1105

let report_implicits :
  'Auu____1122 . 'Auu____1122 -> FStar_TypeChecker_Env.implicits -> unit =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun imp  ->
             let uu____1151 =
               let uu____1152 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____1153 =
                 FStar_Syntax_Print.term_to_string
                   (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                 uu____1152 uu____1153 imp.FStar_TypeChecker_Env.imp_reason
                in
             (FStar_Errors.Error_UninstantiatedUnificationVarInTactic,
               uu____1151, (imp.FStar_TypeChecker_Env.imp_range))) is
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
            (let uu____1192 = FStar_ST.op_Bang tacdbg  in
             if uu____1192
             then
               let uu____1212 = FStar_Syntax_Print.term_to_string tactic  in
               FStar_Util.print1 "Typechecking tactic: (%s) {\n" uu____1212
             else ());
            (let uu____1214 =
               FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic  in
             match uu____1214 with
             | (uu____1227,uu____1228,g) ->
                 ((let uu____1231 = FStar_ST.op_Bang tacdbg  in
                   if uu____1231 then FStar_Util.print_string "}\n" else ());
                  FStar_TypeChecker_Rel.force_trivial_guard env g;
                  FStar_Errors.stop_if_err ();
                  (let tau =
                     unembed_tactic_0 FStar_Syntax_Embeddings.e_unit tactic
                      in
                   let uu____1257 =
                     FStar_TypeChecker_Env.clear_expected_typ env  in
                   match uu____1257 with
                   | (env1,uu____1271) ->
                       let env2 =
                         let uu___340_1277 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___340_1277.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___340_1277.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___340_1277.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___340_1277.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___340_1277.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___340_1277.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___340_1277.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___340_1277.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___340_1277.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___340_1277.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___340_1277.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp = false;
                           FStar_TypeChecker_Env.effects =
                             (uu___340_1277.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___340_1277.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___340_1277.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___340_1277.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___340_1277.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___340_1277.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___340_1277.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___340_1277.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___340_1277.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___340_1277.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___340_1277.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___340_1277.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___340_1277.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___340_1277.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___340_1277.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___340_1277.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___340_1277.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___340_1277.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___340_1277.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___340_1277.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___340_1277.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___340_1277.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___340_1277.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___340_1277.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___340_1277.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___340_1277.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___340_1277.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___340_1277.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___340_1277.FStar_TypeChecker_Env.dep_graph)
                         }  in
                       let env3 =
                         let uu___341_1279 = env2  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___341_1279.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___341_1279.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___341_1279.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___341_1279.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___341_1279.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___341_1279.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___341_1279.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___341_1279.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___341_1279.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___341_1279.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___341_1279.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___341_1279.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___341_1279.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___341_1279.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___341_1279.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___341_1279.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___341_1279.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___341_1279.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___341_1279.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___341_1279.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___341_1279.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes = true;
                           FStar_TypeChecker_Env.phase1 =
                             (uu___341_1279.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___341_1279.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___341_1279.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___341_1279.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___341_1279.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___341_1279.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___341_1279.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___341_1279.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___341_1279.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___341_1279.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___341_1279.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___341_1279.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___341_1279.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___341_1279.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___341_1279.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___341_1279.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___341_1279.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___341_1279.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___341_1279.FStar_TypeChecker_Env.dep_graph)
                         }  in
                       let env4 =
                         let uu___342_1281 = env3  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___342_1281.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___342_1281.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___342_1281.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___342_1281.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___342_1281.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___342_1281.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___342_1281.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___342_1281.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___342_1281.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___342_1281.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___342_1281.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___342_1281.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___342_1281.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___342_1281.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___342_1281.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___342_1281.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___342_1281.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___342_1281.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___342_1281.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___342_1281.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax =
                             (uu___342_1281.FStar_TypeChecker_Env.lax);
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___342_1281.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___342_1281.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard = true;
                           FStar_TypeChecker_Env.nosynth =
                             (uu___342_1281.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___342_1281.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___342_1281.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___342_1281.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___342_1281.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___342_1281.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___342_1281.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___342_1281.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___342_1281.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___342_1281.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___342_1281.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___342_1281.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___342_1281.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___342_1281.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___342_1281.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___342_1281.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___342_1281.FStar_TypeChecker_Env.dep_graph)
                         }  in
                       let rng =
                         let uu____1283 = FStar_Range.use_range rng_goal  in
                         let uu____1284 = FStar_Range.use_range rng_tac  in
                         FStar_Range.range_of_rng uu____1283 uu____1284  in
                       let uu____1285 =
                         FStar_Tactics_Basic.proofstate_of_goal_ty rng env4
                           typ
                          in
                       (match uu____1285 with
                        | (ps,w) ->
                            (FStar_ST.op_Colon_Equals
                               FStar_Reflection_Basic.env_hook
                               (FStar_Pervasives_Native.Some env4);
                             (let uu____1323 = FStar_ST.op_Bang tacdbg  in
                              if uu____1323
                              then
                                let uu____1343 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1
                                  "Running tactic with goal = (%s) {\n"
                                  uu____1343
                              else ());
                             (let uu____1345 =
                                FStar_Util.record_time
                                  (fun uu____1355  ->
                                     FStar_Tactics_Basic.run_safe tau ps)
                                 in
                              match uu____1345 with
                              | (res,ms) ->
                                  ((let uu____1369 = FStar_ST.op_Bang tacdbg
                                       in
                                    if uu____1369
                                    then
                                      let uu____1389 =
                                        FStar_Syntax_Print.term_to_string
                                          tactic
                                         in
                                      let uu____1390 =
                                        FStar_Util.string_of_int ms  in
                                      let uu____1391 =
                                        FStar_Syntax_Print.lid_to_string
                                          env4.FStar_TypeChecker_Env.curmodule
                                         in
                                      FStar_Util.print3
                                        "}\nTactic %s ran in %s ms (%s)\n"
                                        uu____1389 uu____1390 uu____1391
                                    else ());
                                   (match res with
                                    | FStar_Tactics_Result.Success
                                        (uu____1399,ps1) ->
                                        ((let uu____1402 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1402
                                          then
                                            let uu____1422 =
                                              FStar_Syntax_Print.term_to_string
                                                w
                                               in
                                            FStar_Util.print1
                                              "Tactic generated proofterm %s\n"
                                              uu____1422
                                          else ());
                                         FStar_List.iter
                                           (fun g1  ->
                                              let uu____1429 =
                                                FStar_Tactics_Basic.is_irrelevant
                                                  g1
                                                 in
                                              if uu____1429
                                              then
                                                let uu____1430 =
                                                  let uu____1431 =
                                                    FStar_Tactics_Types.goal_env
                                                      g1
                                                     in
                                                  let uu____1432 =
                                                    FStar_Tactics_Types.goal_witness
                                                      g1
                                                     in
                                                  FStar_TypeChecker_Rel.teq_nosmt
                                                    uu____1431 uu____1432
                                                    FStar_Syntax_Util.exp_unit
                                                   in
                                                (if uu____1430
                                                 then ()
                                                 else
                                                   (let uu____1434 =
                                                      let uu____1435 =
                                                        let uu____1436 =
                                                          FStar_Tactics_Types.goal_witness
                                                            g1
                                                           in
                                                        FStar_Syntax_Print.term_to_string
                                                          uu____1436
                                                         in
                                                      FStar_Util.format1
                                                        "Irrelevant tactic witness does not unify with (): %s"
                                                        uu____1435
                                                       in
                                                    failwith uu____1434))
                                              else ())
                                           (FStar_List.append
                                              ps1.FStar_Tactics_Types.goals
                                              ps1.FStar_Tactics_Types.smt_goals);
                                         (let uu____1439 =
                                            FStar_ST.op_Bang tacdbg  in
                                          if uu____1439
                                          then
                                            let uu____1459 =
                                              FStar_Common.string_of_list
                                                (fun imp  ->
                                                   FStar_Syntax_Print.ctx_uvar_to_string
                                                     imp.FStar_TypeChecker_Env.imp_uvar)
                                                ps1.FStar_Tactics_Types.all_implicits
                                               in
                                            FStar_Util.print1
                                              "About to check tactic implicits: %s\n"
                                              uu____1459
                                          else ());
                                         (let g1 =
                                            let uu___343_1464 =
                                              FStar_TypeChecker_Env.trivial_guard
                                               in
                                            {
                                              FStar_TypeChecker_Env.guard_f =
                                                (uu___343_1464.FStar_TypeChecker_Env.guard_f);
                                              FStar_TypeChecker_Env.deferred
                                                =
                                                (uu___343_1464.FStar_TypeChecker_Env.deferred);
                                              FStar_TypeChecker_Env.univ_ineqs
                                                =
                                                (uu___343_1464.FStar_TypeChecker_Env.univ_ineqs);
                                              FStar_TypeChecker_Env.implicits
                                                =
                                                (ps1.FStar_Tactics_Types.all_implicits)
                                            }  in
                                          let g2 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env4 g1
                                             in
                                          (let uu____1467 =
                                             FStar_ST.op_Bang tacdbg  in
                                           if uu____1467
                                           then
                                             let uu____1487 =
                                               FStar_Common.string_of_list
                                                 (fun imp  ->
                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                      imp.FStar_TypeChecker_Env.imp_uvar)
                                                 ps1.FStar_Tactics_Types.all_implicits
                                                in
                                             FStar_Util.print1
                                               "Checked (1) implicits: %s\n"
                                               uu____1487
                                           else ());
                                          (let g3 =
                                             FStar_TypeChecker_Rel.resolve_implicits_tac
                                               env4 g2
                                              in
                                           (let uu____1493 =
                                              FStar_ST.op_Bang tacdbg  in
                                            if uu____1493
                                            then
                                              let uu____1513 =
                                                FStar_Common.string_of_list
                                                  (fun imp  ->
                                                     FStar_Syntax_Print.ctx_uvar_to_string
                                                       imp.FStar_TypeChecker_Env.imp_uvar)
                                                  ps1.FStar_Tactics_Types.all_implicits
                                                 in
                                              FStar_Util.print1
                                                "Checked (2) implicits: %s\n"
                                                uu____1513
                                            else ());
                                           report_implicits ps1
                                             g3.FStar_TypeChecker_Env.implicits;
                                           ((FStar_List.append
                                               ps1.FStar_Tactics_Types.goals
                                               ps1.FStar_Tactics_Types.smt_goals),
                                             w))))
                                    | FStar_Tactics_Result.Failed (s,ps1) ->
                                        ((let uu____1523 =
                                            let uu____1524 =
                                              FStar_TypeChecker_Normalize.psc_subst
                                                ps1.FStar_Tactics_Types.psc
                                               in
                                            FStar_Tactics_Types.subst_proof_state
                                              uu____1524 ps1
                                             in
                                          FStar_Tactics_Basic.dump_proofstate
                                            uu____1523
                                            "at the time of failure");
                                         (let uu____1525 =
                                            let uu____1530 =
                                              FStar_Util.format1
                                                "user tactic failed: %s" s
                                               in
                                            (FStar_Errors.Fatal_UserTacticFailure,
                                              uu____1530)
                                             in
                                          FStar_Errors.raise_error uu____1525
                                            ps1.FStar_Tactics_Types.entry_range))))))))))
  
type pol =
  | Pos 
  | Neg 
  | Both 
let (uu___is_Pos : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Pos  -> true | uu____1542 -> false 
let (uu___is_Neg : pol -> Prims.bool) =
  fun projectee  -> match projectee with | Neg  -> true | uu____1548 -> false 
let (uu___is_Both : pol -> Prims.bool) =
  fun projectee  ->
    match projectee with | Both  -> true | uu____1554 -> false
  
type 'a tres_m =
  | Unchanged of 'a 
  | Simplified of ('a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Dual of ('a,'a,FStar_Tactics_Basic.goal Prims.list)
  FStar_Pervasives_Native.tuple3 
let uu___is_Unchanged : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____1609 -> false
  
let __proj__Unchanged__item___0 : 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0 
let uu___is_Simplified : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____1649 -> false
  
let __proj__Simplified__item___0 :
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Basic.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0 
let uu___is_Dual : 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____1703 -> false
  
let __proj__Dual__item___0 :
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Basic.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0 
type tres = FStar_Syntax_Syntax.term tres_m
let tpure : 'Auu____1744 . 'Auu____1744 -> 'Auu____1744 tres_m =
  fun x  -> Unchanged x 
let (flip : pol -> pol) =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both 
let (by_tactic_interp :
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____1772 = FStar_Syntax_Util.head_and_args t  in
        match uu____1772 with
        | (hd1,args) ->
            let uu____1815 =
              let uu____1830 =
                let uu____1831 = FStar_Syntax_Util.un_uinst hd1  in
                uu____1831.FStar_Syntax_Syntax.n  in
              (uu____1830, args)  in
            (match uu____1815 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1846))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____1909 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1909 with
                       | (gs,uu____1917) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____1924 =
                        run_tactic_on_typ tactic.FStar_Syntax_Syntax.pos
                          assertion.FStar_Syntax_Syntax.pos tactic e
                          assertion
                         in
                      (match uu____1924 with
                       | (gs,uu____1932) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____1975 =
                        let uu____1982 =
                          let uu____1985 =
                            let uu____1986 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____1986
                             in
                          [uu____1985]  in
                        (FStar_Syntax_Util.t_true, uu____1982)  in
                      Simplified uu____1975
                  | Both  ->
                      let uu____1997 =
                        let uu____2006 =
                          let uu____2009 =
                            let uu____2010 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion
                               in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____2010
                             in
                          [uu____2009]  in
                        (assertion, FStar_Syntax_Util.t_true, uu____2006)  in
                      Dual uu____1997
                  | Neg  -> Simplified (assertion, []))
             | uu____2023 -> Unchanged t)
  
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
    fun uu___339_2113  ->
      match uu___339_2113 with
      | Unchanged t -> let uu____2119 = f t  in Unchanged uu____2119
      | Simplified (t,gs) ->
          let uu____2126 = let uu____2133 = f t  in (uu____2133, gs)  in
          Simplified uu____2126
      | Dual (tn,tp,gs) ->
          let uu____2143 =
            let uu____2152 = f tn  in
            let uu____2153 = f tp  in (uu____2152, uu____2153, gs)  in
          Dual uu____2143
  
let comb2 :
  'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____2216 = f t1 t2  in Unchanged uu____2216
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____2228 = let uu____2235 = f t1 t2  in (uu____2235, gs)
               in
            Simplified uu____2228
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____2249 = let uu____2256 = f t1 t2  in (uu____2256, gs)
               in
            Simplified uu____2249
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____2275 =
              let uu____2282 = f t1 t2  in
              (uu____2282, (FStar_List.append gs1 gs2))  in
            Simplified uu____2275
        | uu____2285 ->
            let uu____2294 = explode x  in
            (match uu____2294 with
             | (n1,p1,gs1) ->
                 let uu____2312 = explode y  in
                 (match uu____2312 with
                  | (n2,p2,gs2) ->
                      let uu____2330 =
                        let uu____2339 = f n1 n2  in
                        let uu____2340 = f p1 p2  in
                        (uu____2339, uu____2340, (FStar_List.append gs1 gs2))
                         in
                      Dual uu____2330))
  
let comb_list : 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____2412 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc  in
          aux tl1 uu____2412
       in
    aux (FStar_List.rev rs) (tpure [])
  
let emit : 'a . FStar_Tactics_Basic.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____2460  -> fun x  -> x) (Simplified ((), gs)) m
  
let rec (traverse :
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____2502 =
              let uu____2503 = FStar_Syntax_Subst.compress t  in
              uu____2503.FStar_Syntax_Syntax.n  in
            match uu____2502 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1  in
                let uu____2515 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us))
                   in
                uu____2515 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1  in
                let uu____2541 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m))  in
                uu____2541 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2561;
                   FStar_Syntax_Syntax.vars = uu____2562;_},(p,uu____2564)::
                 (q,uu____2566)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____2622 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2622
                   in
                let r1 = traverse f (flip pol) e p  in
                let r2 =
                  let uu____2625 = FStar_TypeChecker_Env.push_bv e x  in
                  traverse f pol uu____2625 q  in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____2639 = FStar_Syntax_Util.mk_imp l r  in
                       uu____2639.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____2643;
                   FStar_Syntax_Syntax.vars = uu____2644;_},(p,uu____2646)::
                 (q,uu____2648)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____2704 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2704
                   in
                let xq =
                  let uu____2706 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q
                     in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____2706
                   in
                let r1 =
                  let uu____2708 = FStar_TypeChecker_Env.push_bv e xq  in
                  traverse f Both uu____2708 p  in
                let r2 =
                  let uu____2710 = FStar_TypeChecker_Env.push_bv e xp  in
                  traverse f Both uu____2710 q  in
                (match (r1, r2) with
                 | (Unchanged uu____2717,Unchanged uu____2718) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____2736 = FStar_Syntax_Util.mk_iff l r  in
                            uu____2736.FStar_Syntax_Syntax.n) r1 r2
                 | uu____2739 ->
                     let uu____2748 = explode r1  in
                     (match uu____2748 with
                      | (pn,pp,gs1) ->
                          let uu____2766 = explode r2  in
                          (match uu____2766 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____2787 =
                                   FStar_Syntax_Util.mk_imp pn qp  in
                                 let uu____2790 =
                                   FStar_Syntax_Util.mk_imp qn pp  in
                                 FStar_Syntax_Util.mk_conj uu____2787
                                   uu____2790
                                  in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1  in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____2854  ->
                       fun r  ->
                         match uu____2854 with
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
                let uu____3006 = FStar_Syntax_Subst.open_term bs t1  in
                (match uu____3006 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1  in
                     let r0 =
                       FStar_List.map
                         (fun uu____3046  ->
                            match uu____3046 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort
                                   in
                                let uu____3068 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___344_3100 = bv  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___344_3100.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___344_3100.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq))
                                   in
                                uu____3068 r) bs1
                        in
                     let rbs = comb_list r0  in
                     let rt = traverse f pol e' topen  in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3128 = FStar_Syntax_Util.abs bs2 t2 k
                               in
                            uu____3128.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____3174 = traverse f pol e t1  in
                let uu____3179 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef))
                   in
                uu____3179 uu____3174
            | x -> tpure x  in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___345_3219 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___345_3219.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___345_3219.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____3226 =
                f pol e
                  (let uu___346_3230 = t  in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___346_3230.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___346_3230.FStar_Syntax_Syntax.vars)
                   })
                 in
              emit gs uu____3226
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___347_3240 = t  in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___347_3240.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___347_3240.FStar_Syntax_Syntax.vars)
                   })
                 in
              let uu____3241 = explode rp  in
              (match uu____3241 with
               | (uu____3250,p',gs') ->
                   Dual
                     ((let uu___348_3260 = t  in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___348_3260.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___348_3260.FStar_Syntax_Syntax.vars)
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
          [FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
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
      (let uu____3303 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
       FStar_ST.op_Colon_Equals tacdbg uu____3303);
      (let uu____3324 = FStar_ST.op_Bang tacdbg  in
       if uu____3324
       then
         let uu____3344 =
           let uu____3345 = FStar_TypeChecker_Env.all_binders env  in
           FStar_All.pipe_right uu____3345
             (FStar_Syntax_Print.binders_to_string ",")
            in
         let uu____3346 = FStar_Syntax_Print.term_to_string goal  in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3344
           uu____3346
       else ());
      (let initial = ((Prims.parse_int "1"), [])  in
       let uu____3375 =
         let uu____3384 = traverse by_tactic_interp Pos env goal  in
         match uu____3384 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____3408 -> failwith "no"  in
       match uu____3375 with
       | (t',gs) ->
           ((let uu____3436 = FStar_ST.op_Bang tacdbg  in
             if uu____3436
             then
               let uu____3456 =
                 let uu____3457 = FStar_TypeChecker_Env.all_binders env  in
                 FStar_All.pipe_right uu____3457
                   (FStar_Syntax_Print.binders_to_string ", ")
                  in
               let uu____3458 = FStar_Syntax_Print.term_to_string t'  in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3456 uu____3458
             else ());
            (let s = initial  in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3506  ->
                    fun g  ->
                      match uu____3506 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3551 =
                              let uu____3554 = FStar_Tactics_Types.goal_env g
                                 in
                              let uu____3555 =
                                FStar_Tactics_Types.goal_type g  in
                              getprop uu____3554 uu____3555  in
                            match uu____3551 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3556 =
                                  let uu____3561 =
                                    let uu____3562 =
                                      let uu____3563 =
                                        FStar_Tactics_Types.goal_type g  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____3563
                                       in
                                    FStar_Util.format1
                                      "Tactic returned proof-relevant goal: %s"
                                      uu____3562
                                     in
                                  (FStar_Errors.Fatal_TacticProofRelevantGoal,
                                    uu____3561)
                                   in
                                FStar_Errors.raise_error uu____3556
                                  env.FStar_TypeChecker_Env.range
                            | FStar_Pervasives_Native.Some phi -> phi  in
                          ((let uu____3566 = FStar_ST.op_Bang tacdbg  in
                            if uu____3566
                            then
                              let uu____3586 = FStar_Util.string_of_int n1
                                 in
                              let uu____3587 =
                                let uu____3588 =
                                  FStar_Tactics_Types.goal_type g  in
                                FStar_Syntax_Print.term_to_string uu____3588
                                 in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____3586 uu____3587
                            else ());
                           (let gt' =
                              let uu____3591 =
                                let uu____3592 = FStar_Util.string_of_int n1
                                   in
                                Prims.strcat "Could not prove goal #"
                                  uu____3592
                                 in
                              FStar_TypeChecker_Util.label uu____3591
                                goal.FStar_Syntax_Syntax.pos phi
                               in
                            let uu____3593 =
                              let uu____3602 =
                                let uu____3609 =
                                  FStar_Tactics_Types.goal_env g  in
                                (uu____3609, gt',
                                  (g.FStar_Tactics_Types.opts))
                                 in
                              uu____3602 :: gs1  in
                            ((n1 + (Prims.parse_int "1")), uu____3593)))) s
                 gs
                in
             let uu____3624 = s1  in
             match uu____3624 with
             | (uu____3645,gs1) ->
                 let uu____3663 =
                   let uu____3670 = FStar_Options.peek ()  in
                   (env, t', uu____3670)  in
                 uu____3663 :: gs1)))
  
let (reify_tactic : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun a  ->
    let r =
      let uu____3683 =
        let uu____3684 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____3684  in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____3683 [FStar_Syntax_Syntax.U_zero]
       in
    let uu____3685 =
      let uu____3690 =
        let uu____3691 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit
           in
        let uu____3700 =
          let uu____3711 = FStar_Syntax_Syntax.as_arg a  in [uu____3711]  in
        uu____3691 :: uu____3700  in
      FStar_Syntax_Syntax.mk_Tm_app r uu____3690  in
    uu____3685 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
  
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
          let uu____3761 =
            let uu____3766 =
              FStar_TypeChecker_Util.fvar_const env
                FStar_Parser_Const.magic_lid
               in
            let uu____3767 =
              let uu____3768 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3768]  in
            FStar_Syntax_Syntax.mk_Tm_app uu____3766 uu____3767  in
          uu____3761 FStar_Pervasives_Native.None typ.FStar_Syntax_Syntax.pos
        else
          ((let uu____3797 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
            FStar_ST.op_Colon_Equals tacdbg uu____3797);
           (let uu____3817 =
              let uu____3824 = reify_tactic tau  in
              run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
                typ.FStar_Syntax_Syntax.pos uu____3824 env typ
               in
            match uu____3817 with
            | (gs,w) ->
                (FStar_List.iter
                   (fun g  ->
                      let uu____3838 =
                        let uu____3841 = FStar_Tactics_Types.goal_env g  in
                        let uu____3842 = FStar_Tactics_Types.goal_type g  in
                        getprop uu____3841 uu____3842  in
                      match uu____3838 with
                      | FStar_Pervasives_Native.Some vc ->
                          let guard =
                            {
                              FStar_TypeChecker_Env.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial vc);
                              FStar_TypeChecker_Env.deferred = [];
                              FStar_TypeChecker_Env.univ_ineqs = ([], []);
                              FStar_TypeChecker_Env.implicits = []
                            }  in
                          let uu____3853 = FStar_Tactics_Types.goal_env g  in
                          FStar_TypeChecker_Rel.force_trivial_guard
                            uu____3853 guard
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
        ((let uu____3870 =
            FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac")  in
          FStar_ST.op_Colon_Equals tacdbg uu____3870);
         (let typ = FStar_Syntax_Syntax.t_decls  in
          let uu____3891 =
            let uu____3898 = reify_tactic tau  in
            run_tactic_on_typ tau.FStar_Syntax_Syntax.pos
              tau.FStar_Syntax_Syntax.pos uu____3898 env typ
             in
          match uu____3891 with
          | (gs,w) ->
              ((let uu____3908 =
                  FStar_List.existsML
                    (fun g  ->
                       let uu____3912 =
                         let uu____3913 =
                           let uu____3916 = FStar_Tactics_Types.goal_env g
                              in
                           let uu____3917 = FStar_Tactics_Types.goal_type g
                              in
                           getprop uu____3916 uu____3917  in
                         FStar_Option.isSome uu____3913  in
                       Prims.op_Negation uu____3912) gs
                   in
                if uu____3908
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                      "splice left open goals") typ.FStar_Syntax_Syntax.pos
                else ());
               (let w1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Weak;
                    FStar_TypeChecker_Normalize.HNF;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant;
                    FStar_TypeChecker_Normalize.Primops;
                    FStar_TypeChecker_Normalize.Unascribe;
                    FStar_TypeChecker_Normalize.Unmeta] env w
                   in
                (let uu____3921 = FStar_ST.op_Bang tacdbg  in
                 if uu____3921
                 then
                   let uu____3941 = FStar_Syntax_Print.term_to_string w1  in
                   FStar_Util.print1 "splice: got witness = %s\n" uu____3941
                 else ());
                (let uu____3943 =
                   let uu____3948 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Reflection_Embeddings.e_sigelt
                      in
                   FStar_Syntax_Embeddings.unembed uu____3948 w1  in
                 match uu____3943 with
                 | FStar_Pervasives_Native.Some sigelts -> sigelts
                 | FStar_Pervasives_Native.None  ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_SpliceUnembedFail,
                         "splice: failed to unembed sigelts")
                       typ.FStar_Syntax_Syntax.pos)))))
  