open Prims
type name = FStar_Syntax_Syntax.bv
let remove_unit f x = f x ()
let quote:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | uu____33::(y,uu____35)::[] ->
          let uu____56 = FStar_Tactics_Embedding.embed_term y in
          Some uu____56
      | uu____57 -> None
let binders_of_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (embedded_env,uu____70)::[] ->
            let env =
              FStar_Tactics_Embedding.unembed_env
                ps.FStar_Tactics_Basic.main_context embedded_env in
            let uu____84 =
              let uu____85 = FStar_TypeChecker_Env.all_binders env in
              FStar_Tactics_Embedding.embed_binders uu____85 in
            Some uu____84
        | uu____87 -> None
let type_of_binder:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_binder,uu____97)::[] ->
          let uu____110 =
            FStar_Tactics_Embedding.unembed_binder embedded_binder in
          (match uu____110 with
           | (b,uu____113) ->
               let uu____114 =
                 FStar_Tactics_Embedding.embed_term
                   b.FStar_Syntax_Syntax.sort in
               Some uu____114)
      | uu____115 -> None
let term_eq:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_t1,uu____125)::(embedded_t2,uu____127)::[] ->
          let t1 = FStar_Tactics_Embedding.unembed_term embedded_t1 in
          let t2 = FStar_Tactics_Embedding.unembed_term embedded_t2 in
          let b = FStar_Syntax_Util.term_eq t1 t2 in
          let uu____151 = FStar_Tactics_Embedding.embed_bool b in
          Some uu____151
      | uu____152 -> None
let mk_pure_interpretation_2 f unembed_a unembed_b embed_c nm args =
  (let uu____216 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____216
   then
     let uu____219 = FStar_Ident.string_of_lid nm in
     let uu____220 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____219 uu____220
   else ());
  (match args with
   | (a,uu____224)::(b,uu____226)::[] ->
       let uu____247 =
         let uu____248 =
           let uu____249 = unembed_a a in
           let uu____250 = unembed_b b in f uu____249 uu____250 in
         embed_c uu____248 in
       Some uu____247
   | uu____251 -> failwith "Unexpected interpretation of pure primitive")
let mk_pure_interpretation_1 f unembed_a embed_b nm args =
  (let uu____299 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____299
   then
     let uu____302 = FStar_Ident.string_of_lid nm in
     let uu____303 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____302 uu____303
   else ());
  (match args with
   | a::[] ->
       let uu____319 =
         let uu____320 =
           let uu____321 = unembed_a (Prims.fst a) in f uu____321 in
         embed_b uu____320 in
       Some uu____319
   | uu____324 -> failwith "Unexpected interpretation of pure primitive")
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____367)::[] ->
      ((let uu____381 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____381
        then
          let uu____384 = FStar_Ident.string_of_lid nm in
          let uu____385 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.print2 "Reached %s, args are: %s\n" uu____384 uu____385
        else ());
       (let uu____387 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____387 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_396 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_396.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_396.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_396.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___108_396.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____399 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____399))
  | uu____400 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____460)::(embedded_state,uu____462)::[] ->
      ((let uu____484 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____484
        then
          let uu____487 = FStar_Ident.string_of_lid nm in
          let uu____488 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____487 uu____488
        else ());
       (let uu____490 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____490 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_499 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_499.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_499.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_499.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___109_499.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____502 = let uu____504 = unembed_b b in t uu____504 in
              FStar_Tactics_Basic.run uu____502 ps1 in
            let uu____505 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____505))
  | uu____506 ->
      let uu____507 =
        let uu____508 = FStar_Ident.string_of_lid nm in
        let uu____509 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____508 uu____509 in
      failwith uu____507
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____586)::(b,uu____588)::(embedded_state,uu____590)::[] ->
      ((let uu____620 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____620
        then
          let uu____623 = FStar_Ident.string_of_lid nm in
          let uu____624 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____623 uu____624
        else ());
       (let uu____626 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____626 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_635 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_635.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_635.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_635.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___110_635.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____638 =
                let uu____640 = unembed_a a in
                let uu____641 = unembed_b b in t uu____640 uu____641 in
              FStar_Tactics_Basic.run uu____638 ps1 in
            let uu____642 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            Some uu____642))
  | uu____643 ->
      let uu____644 =
        let uu____645 = FStar_Ident.string_of_lid nm in
        let uu____646 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____645 uu____646 in
      failwith uu____644
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____661)::(et2,uu____663)::(embedded_state,uu____665)::[] ->
            let uu____694 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____694 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___111_703 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___111_703.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___111_703.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___111_703.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___111_703.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____706 =
                     let uu____708 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____709 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____710 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____711 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____708 uu____709
                       uu____710 uu____711 in
                   FStar_Tactics_Basic.run uu____706 ps1 in
                 let uu____712 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____712)
        | uu____713 ->
            let uu____714 =
              let uu____715 = FStar_Ident.string_of_lid nm in
              let uu____716 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____715
                uu____716 in
            failwith uu____714
let rec primitive_steps:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  fun ps  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid nm in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      } in
    let uu____762 =
      mk1 "__forall_intros" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____763 =
      let uu____765 =
        mk1 "__implies_intro" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____766 =
        let uu____768 =
          mk1 "__trivial" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____769 =
          let uu____771 =
            mk1 "__revert" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____772 =
            let uu____774 =
              mk1 "__clear" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____775 =
              let uu____777 =
                mk1 "__split" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____778 =
                let uu____780 =
                  mk1 "__merge" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____781 =
                  let uu____783 =
                    mk1 "__rewrite" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____784 =
                    let uu____786 =
                      mk1 "__smt" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____787 =
                      let uu____789 =
                        mk1 "__exact" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____790 =
                        let uu____792 =
                          mk1 "__apply_lemma" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____793 =
                          let uu____795 =
                            mk1 "__visit" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____797 =
                            let uu____799 =
                              mk1 "__focus" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____801 =
                              let uu____803 =
                                mk1 "__seq" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____806 =
                                let uu____808 =
                                  mk1 "__term_as_formula"
                                    (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____810 =
                                  let uu____812 =
                                    mk1 "__inspect" (Prims.parse_int "1")
                                      (mk_pure_interpretation_1
                                         FStar_Tactics_Embedding.inspect
                                         FStar_Tactics_Embedding.unembed_term
                                         (FStar_Tactics_Embedding.embed_option
                                            FStar_Tactics_Embedding.embed_term_view
                                            FStar_Tactics_Embedding.fstar_tactics_term_view)) in
                                  let uu____814 =
                                    let uu____816 =
                                      mk1 "__pack" (Prims.parse_int "1")
                                        (mk_pure_interpretation_1
                                           FStar_Tactics_Embedding.pack
                                           FStar_Tactics_Embedding.unembed_term_view
                                           FStar_Tactics_Embedding.embed_term) in
                                    let uu____817 =
                                      let uu____819 =
                                        mk1 "__inspect_fv"
                                          (Prims.parse_int "1")
                                          (mk_pure_interpretation_1
                                             FStar_Tactics_Embedding.inspectfv
                                             FStar_Tactics_Embedding.unembed_fvar
                                             (FStar_Tactics_Embedding.embed_list
                                                FStar_Tactics_Embedding.embed_string
                                                FStar_TypeChecker_Common.t_string)) in
                                      let uu____821 =
                                        let uu____823 =
                                          mk1 "__pack_fv"
                                            (Prims.parse_int "1")
                                            (mk_pure_interpretation_1
                                               FStar_Tactics_Embedding.packfv
                                               (FStar_Tactics_Embedding.unembed_list
                                                  FStar_Tactics_Embedding.unembed_string)
                                               FStar_Tactics_Embedding.embed_fvar) in
                                        let uu____825 =
                                          let uu____827 =
                                            mk1 "__inspect_bv"
                                              (Prims.parse_int "1")
                                              (mk_pure_interpretation_1
                                                 FStar_Tactics_Embedding.inspectbv
                                                 FStar_Tactics_Embedding.unembed_binder
                                                 FStar_Tactics_Embedding.embed_string) in
                                          let uu____828 =
                                            let uu____830 =
                                              mk1 "__compare_binder"
                                                (Prims.parse_int "2")
                                                (mk_pure_interpretation_2
                                                   FStar_Tactics_Basic.order_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.embed_order) in
                                            let uu____831 =
                                              let uu____833 =
                                                mk1 "__binders_of_env"
                                                  (Prims.parse_int "1")
                                                  (binders_of_env ps) in
                                              let uu____834 =
                                                let uu____836 =
                                                  mk1 "__type_of_binder"
                                                    (Prims.parse_int "1")
                                                    type_of_binder in
                                                let uu____837 =
                                                  let uu____839 =
                                                    mk1 "__term_eq"
                                                      (Prims.parse_int "2")
                                                      term_eq in
                                                  let uu____840 =
                                                    let uu____842 =
                                                      mk1 "__print"
                                                        (Prims.parse_int "2")
                                                        (mk_tactic_interpretation_1
                                                           ps
                                                           (fun x  ->
                                                              FStar_Tactics_Basic.tacprint
                                                                x;
                                                              FStar_Tactics_Basic.ret
                                                                ())
                                                           FStar_Tactics_Embedding.unembed_string
                                                           FStar_Tactics_Embedding.embed_unit
                                                           FStar_TypeChecker_Common.t_unit) in
                                                    let uu____845 =
                                                      let uu____847 =
                                                        mk1 "__dump"
                                                          (Prims.parse_int
                                                             "2")
                                                          (mk_tactic_interpretation_1
                                                             ps
                                                             FStar_Tactics_Basic.print_proof_state
                                                             FStar_Tactics_Embedding.unembed_string
                                                             FStar_Tactics_Embedding.embed_unit
                                                             FStar_TypeChecker_Common.t_unit) in
                                                      let uu____848 =
                                                        let uu____850 =
                                                          mk1
                                                            "__term_to_string"
                                                            (Prims.parse_int
                                                               "1")
                                                            (mk_pure_interpretation_1
                                                               FStar_Syntax_Print.term_to_string
                                                               FStar_Tactics_Embedding.unembed_term
                                                               FStar_Tactics_Embedding.embed_string) in
                                                        let uu____851 =
                                                          let uu____853 =
                                                            mk1 "__grewrite"
                                                              (Prims.parse_int
                                                                 "3")
                                                              (grewrite_interpretation
                                                                 ps) in
                                                          [uu____853] in
                                                        uu____850 ::
                                                          uu____851 in
                                                      uu____847 :: uu____848 in
                                                    uu____842 :: uu____845 in
                                                  uu____839 :: uu____840 in
                                                uu____836 :: uu____837 in
                                              uu____833 :: uu____834 in
                                            uu____830 :: uu____831 in
                                          uu____827 :: uu____828 in
                                        uu____823 :: uu____825 in
                                      uu____819 :: uu____821 in
                                    uu____816 :: uu____817 in
                                  uu____812 :: uu____814 in
                                uu____808 :: uu____810 in
                              uu____803 :: uu____806 in
                            uu____799 :: uu____801 in
                          uu____795 :: uu____797 in
                        uu____792 :: uu____793 in
                      uu____789 :: uu____790 in
                    uu____786 :: uu____787 in
                  uu____783 :: uu____784 in
                uu____780 :: uu____781 in
              uu____777 :: uu____778 in
            uu____774 :: uu____775 in
          uu____771 :: uu____772 in
        uu____768 :: uu____769 in
      uu____765 :: uu____766 in
    uu____762 :: uu____763
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____862 =
           let uu____863 =
             let uu____864 =
               let uu____865 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____865 in
             [uu____864] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____863 in
         uu____862 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____874 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____879  ->
              let uu____880 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____880) in
       FStar_Tactics_Basic.bind uu____874
         (fun uu____881  ->
            let result =
              let uu____883 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____883 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____885 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____890  ->
                   let uu____891 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____891) in
            FStar_Tactics_Basic.bind uu____885
              (fun uu____892  ->
                 let uu____893 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____893 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____920  ->
                          let uu____921 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____921
                            (fun uu____923  ->
                               let uu____924 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____924
                                 (fun uu____926  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____946  ->
                          let uu____947 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____947
                            (fun uu____949  ->
                               let uu____950 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____950
                                 (fun uu____952  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____956 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____956 with
            | (hd1,args) ->
                let uu____983 =
                  let uu____991 =
                    let uu____992 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____992.FStar_Syntax_Syntax.n in
                  (uu____991, args) in
                (match uu____983 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____1003)::(assertion,uu____1005)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____1031 =
                       let uu____1033 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___112_1035 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___112_1035.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___112_1035.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____1033
                         (fun uu____1036  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____1031
                 | uu____1037 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____1057 = FStar_Syntax_Util.head_and_args t in
      match uu____1057 with
      | (hd1,args) ->
          let uu____1086 =
            let uu____1094 =
              let uu____1095 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1095.FStar_Syntax_Syntax.n in
            (uu____1094, args) in
          (match uu____1086 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____1108)::(assertion,uu____1110)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____1136 =
                 let uu____1138 =
                   unembed_tactic_0 FStar_Tactics_Embedding.unembed_unit
                     tactic in
                 let uu____1140 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____1138 uu____1140 in
               (match uu____1136 with
                | FStar_Tactics_Basic.Success (uu____1144,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____1152 -> (t, []))
let rec traverse:
  (FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list))
    ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun f  ->
    fun e  ->
      fun t  ->
        let uu____1192 =
          let uu____1196 =
            let uu____1197 = FStar_Syntax_Subst.compress t in
            uu____1197.FStar_Syntax_Syntax.n in
          match uu____1196 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1209 = traverse f e t1 in
              (match uu____1209 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1227 = traverse f e t1 in
              (match uu____1227 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1240;
                 FStar_Syntax_Syntax.pos = uu____1241;
                 FStar_Syntax_Syntax.vars = uu____1242;_},(p,uu____1244)::
               (q,uu____1246)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1277 =
                let uu____1281 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1281 q in
              (match uu____1277 with
               | (q',gs) ->
                   let uu____1289 =
                     let uu____1290 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1290.FStar_Syntax_Syntax.n in
                   (uu____1289, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1310 = traverse f e hd1 in
              (match uu____1310 with
               | (hd',gs1) ->
                   let uu____1321 =
                     FStar_List.fold_right
                       (fun uu____1336  ->
                          fun uu____1337  ->
                            match (uu____1336, uu____1337) with
                            | ((a,q),(as',gs)) ->
                                let uu____1380 = traverse f e a in
                                (match uu____1380 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1321 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1448 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1448 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1457 = traverse f e' topen in
                   (match uu____1457 with
                    | (topen',gs) ->
                        let uu____1468 =
                          let uu____1469 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1469.FStar_Syntax_Syntax.n in
                        (uu____1468, gs)))
          | x -> (x, []) in
        match uu____1192 with
        | (tn',gs) ->
            let t' =
              let uu___113_1485 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___113_1485.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___113_1485.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___113_1485.FStar_Syntax_Syntax.vars)
              } in
            let uu____1490 = f e t' in
            (match uu____1490 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1515 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1515);
      (let uu____1519 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1519
       then
         let uu____1522 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1522
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1535 = traverse by_tactic_interp env goal in
       match uu____1535 with
       | (t',gs) ->
           ((let uu____1547 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1547
             then
               let uu____1550 =
                 let uu____1551 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1551
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1552 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1550 uu____1552
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1571  ->
                    fun g  ->
                      match uu____1571 with
                      | (n1,gs1) ->
                          ((let uu____1592 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1592
                            then
                              let uu____1595 = FStar_Util.string_of_int n1 in
                              let uu____1596 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1595 uu____1596
                            else ());
                           (let gt' =
                              let uu____1599 =
                                let uu____1600 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1600 in
                              FStar_TypeChecker_Util.label uu____1599
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1606 = s1 in
             match uu____1606 with | (uu____1615,gs1) -> (env, t') :: gs1)))