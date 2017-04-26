open Prims
type name = FStar_Syntax_Syntax.bv
let remove_unit f x = f x ()
let binders_of_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (embedded_env,uu____37)::[] ->
            let env =
              FStar_Tactics_Embedding.unembed_env
                ps.FStar_Tactics_Basic.main_context embedded_env in
            let uu____51 =
              let uu____52 = FStar_TypeChecker_Env.all_binders env in
              FStar_Tactics_Embedding.embed_binders uu____52 in
            Some uu____51
        | uu____54 -> None
let type_of_binder:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_binder,uu____64)::[] ->
          let uu____77 =
            FStar_Tactics_Embedding.unembed_binder embedded_binder in
          (match uu____77 with
           | (b,uu____80) ->
               let uu____81 =
                 FStar_Tactics_Embedding.embed_term
                   b.FStar_Syntax_Syntax.sort in
               Some uu____81)
      | uu____82 -> None
let term_eq:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_t1,uu____92)::(embedded_t2,uu____94)::[] ->
          let t1 = FStar_Tactics_Embedding.unembed_term embedded_t1 in
          let t2 = FStar_Tactics_Embedding.unembed_term embedded_t2 in
          let uu____117 = FStar_Syntax_Util.eq_tm t1 t2 in
          (match uu____117 with
           | FStar_Syntax_Util.Equal  ->
               let uu____119 = FStar_Tactics_Embedding.embed_bool true in
               Some uu____119
           | uu____120 ->
               let uu____121 = FStar_Tactics_Embedding.embed_bool false in
               Some uu____121)
      | uu____122 -> None
let mk_pure_interpretation_1 f unembed_a embed_b nm args =
  match args with
  | a::[] ->
      let uu____183 =
        let uu____184 =
          let uu____185 = unembed_a (Prims.fst a) in f uu____185 in
        embed_b uu____184 in
      Some uu____183
  | uu____188 -> failwith "Unexpected interpretation of pure primitive"
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____231)::[] ->
      let uu____244 =
        FStar_Tactics_Embedding.unembed_state
          ps.FStar_Tactics_Basic.main_context embedded_state in
      (match uu____244 with
       | (goals,smt_goals) ->
           let ps1 =
             let uu___104_253 = ps in
             {
               FStar_Tactics_Basic.main_context =
                 (uu___104_253.FStar_Tactics_Basic.main_context);
               FStar_Tactics_Basic.main_goal =
                 (uu___104_253.FStar_Tactics_Basic.main_goal);
               FStar_Tactics_Basic.all_implicits =
                 (uu___104_253.FStar_Tactics_Basic.all_implicits);
               FStar_Tactics_Basic.goals = goals;
               FStar_Tactics_Basic.smt_goals = smt_goals;
               FStar_Tactics_Basic.transaction =
                 (uu___104_253.FStar_Tactics_Basic.transaction)
             } in
           let res = FStar_Tactics_Basic.run t ps1 in
           let uu____256 =
             FStar_Tactics_Embedding.embed_result res embed_a t_a in
           Some uu____256)
  | uu____257 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____317)::(embedded_state,uu____319)::[] ->
      let uu____340 =
        FStar_Tactics_Embedding.unembed_state
          ps.FStar_Tactics_Basic.main_context embedded_state in
      (match uu____340 with
       | (goals,smt_goals) ->
           let ps1 =
             let uu___105_349 = ps in
             {
               FStar_Tactics_Basic.main_context =
                 (uu___105_349.FStar_Tactics_Basic.main_context);
               FStar_Tactics_Basic.main_goal =
                 (uu___105_349.FStar_Tactics_Basic.main_goal);
               FStar_Tactics_Basic.all_implicits =
                 (uu___105_349.FStar_Tactics_Basic.all_implicits);
               FStar_Tactics_Basic.goals = goals;
               FStar_Tactics_Basic.smt_goals = smt_goals;
               FStar_Tactics_Basic.transaction =
                 (uu___105_349.FStar_Tactics_Basic.transaction)
             } in
           let res =
             let uu____352 = let uu____354 = unembed_b b in t uu____354 in
             FStar_Tactics_Basic.run uu____352 ps1 in
           let uu____355 =
             FStar_Tactics_Embedding.embed_result res embed_a t_a in
           Some uu____355)
  | uu____356 ->
      let uu____357 =
        let uu____358 = FStar_Ident.string_of_lid nm in
        let uu____359 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____358 uu____359 in
      failwith uu____357
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____436)::(b,uu____438)::(embedded_state,uu____440)::[] ->
      let uu____469 =
        FStar_Tactics_Embedding.unembed_state
          ps.FStar_Tactics_Basic.main_context embedded_state in
      (match uu____469 with
       | (goals,smt_goals) ->
           let ps1 =
             let uu___106_478 = ps in
             {
               FStar_Tactics_Basic.main_context =
                 (uu___106_478.FStar_Tactics_Basic.main_context);
               FStar_Tactics_Basic.main_goal =
                 (uu___106_478.FStar_Tactics_Basic.main_goal);
               FStar_Tactics_Basic.all_implicits =
                 (uu___106_478.FStar_Tactics_Basic.all_implicits);
               FStar_Tactics_Basic.goals = goals;
               FStar_Tactics_Basic.smt_goals = smt_goals;
               FStar_Tactics_Basic.transaction =
                 (uu___106_478.FStar_Tactics_Basic.transaction)
             } in
           let res =
             let uu____481 =
               let uu____483 = unembed_a a in
               let uu____484 = unembed_b b in t uu____483 uu____484 in
             FStar_Tactics_Basic.run uu____481 ps1 in
           let uu____485 =
             FStar_Tactics_Embedding.embed_result res embed_c t_c in
           Some uu____485)
  | uu____486 ->
      let uu____487 =
        let uu____488 = FStar_Ident.string_of_lid nm in
        let uu____489 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____488 uu____489 in
      failwith uu____487
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____504)::(et2,uu____506)::(embedded_state,uu____508)::[] ->
            let uu____537 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____537 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___107_546 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___107_546.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___107_546.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___107_546.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___107_546.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____549 =
                     let uu____551 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____552 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____553 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____554 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____551 uu____552
                       uu____553 uu____554 in
                   FStar_Tactics_Basic.run uu____549 ps1 in
                 let uu____555 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____555)
        | uu____556 ->
            let uu____557 =
              let uu____558 = FStar_Ident.string_of_lid nm in
              let uu____559 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____558
                uu____559 in
            failwith uu____557
let rec primitive_steps:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  fun ps  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid nm in
      let uu____603 = interpretation nm1 in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = uu____603
      } in
    let uu____607 =
      mk1 "forall_intros_" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____608 =
      let uu____610 =
        mk1 "implies_intro_" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____611 =
        let uu____613 =
          mk1 "trivial_" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____614 =
          let uu____616 =
            mk1 "revert_" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____617 =
            let uu____619 =
              mk1 "clear_" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____620 =
              let uu____622 =
                mk1 "split_" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____623 =
                let uu____625 =
                  mk1 "merge_" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____626 =
                  let uu____628 =
                    mk1 "rewrite_" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____629 =
                    let uu____631 =
                      mk1 "smt_" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____632 =
                      let uu____634 =
                        mk1 "exact_" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____635 =
                        let uu____637 =
                          mk1 "apply_lemma_" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____638 =
                          let uu____640 =
                            mk1 "visit_" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____642 =
                            let uu____644 =
                              mk1 "focus_" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____646 =
                              let uu____648 =
                                mk1 "seq_" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____651 =
                                let uu____653 =
                                  mk1 "term_as_formula_"
                                    (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____655 =
                                  let uu____657 =
                                    mk1 "binders_of_env_"
                                      (Prims.parse_int "1")
                                      (binders_of_env ps) in
                                  let uu____658 =
                                    let uu____660 =
                                      mk1 "type_of_binder_"
                                        (Prims.parse_int "1") type_of_binder in
                                    let uu____661 =
                                      let uu____663 =
                                        mk1 "term_eq_" (Prims.parse_int "2")
                                          term_eq in
                                      let uu____664 =
                                        let uu____666 =
                                          mk1 "print_" (Prims.parse_int "2")
                                            (mk_tactic_interpretation_1 ps
                                               FStar_Tactics_Basic.print_proof_state
                                               FStar_Tactics_Embedding.unembed_string
                                               FStar_Tactics_Embedding.embed_unit
                                               FStar_TypeChecker_Common.t_unit) in
                                        let uu____667 =
                                          let uu____669 =
                                            mk1 "grewrite_"
                                              (Prims.parse_int "3")
                                              (grewrite_interpretation ps) in
                                          [uu____669] in
                                        uu____666 :: uu____667 in
                                      uu____663 :: uu____664 in
                                    uu____660 :: uu____661 in
                                  uu____657 :: uu____658 in
                                uu____653 :: uu____655 in
                              uu____648 :: uu____651 in
                            uu____644 :: uu____646 in
                          uu____640 :: uu____642 in
                        uu____637 :: uu____638 in
                      uu____634 :: uu____635 in
                    uu____631 :: uu____632 in
                  uu____628 :: uu____629 in
                uu____625 :: uu____626 in
              uu____622 :: uu____623 in
            uu____619 :: uu____620 in
          uu____616 :: uu____617 in
        uu____613 :: uu____614 in
      uu____610 :: uu____611 in
    uu____607 :: uu____608
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____678 =
           let uu____679 =
             let uu____680 =
               let uu____681 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____681 in
             [uu____680] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____679 in
         uu____678 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       FStar_Options.set_option "debug_level"
         (FStar_Options.List [FStar_Options.String "Norm"]);
       (let result =
          let uu____692 = primitive_steps proof_state in
          FStar_TypeChecker_Normalize.normalize_with_primitive_steps
            uu____692 steps proof_state.FStar_Tactics_Basic.main_context tm in
        FStar_Options.set_option "debug_level" (FStar_Options.List []);
        (let uu____695 =
           FStar_Tactics_Embedding.unembed_result
             proof_state.FStar_Tactics_Basic.main_context result unembed_b in
         match uu____695 with
         | FStar_Util.Inl (b,(goals,smt_goals)) ->
             FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
               (fun uu____722  ->
                  let uu____723 = FStar_Tactics_Basic.add_goals goals in
                  FStar_Tactics_Basic.bind uu____723
                    (fun uu____725  ->
                       let uu____726 =
                         FStar_Tactics_Basic.add_smt_goals smt_goals in
                       FStar_Tactics_Basic.bind uu____726
                         (fun uu____728  -> FStar_Tactics_Basic.ret b)))
         | FStar_Util.Inr (msg,(goals,smt_goals)) ->
             FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
               (fun uu____748  ->
                  let uu____749 = FStar_Tactics_Basic.add_goals goals in
                  FStar_Tactics_Basic.bind uu____749
                    (fun uu____751  ->
                       let uu____752 =
                         FStar_Tactics_Basic.add_smt_goals smt_goals in
                       FStar_Tactics_Basic.bind uu____752
                         (fun uu____754  -> FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____758 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____758 with
            | (hd1,args) ->
                let uu____785 =
                  let uu____793 =
                    let uu____794 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____794.FStar_Syntax_Syntax.n in
                  (uu____793, args) in
                (match uu____785 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____805)::(assertion,uu____807)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____833 =
                       let uu____835 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___108_837 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___108_837.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___108_837.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____835
                         (fun uu____838  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____833
                 | uu____839 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____859 = FStar_Syntax_Util.head_and_args t in
      match uu____859 with
      | (hd1,args) ->
          let uu____888 =
            let uu____896 =
              let uu____897 = FStar_Syntax_Util.un_uinst hd1 in
              uu____897.FStar_Syntax_Syntax.n in
            (uu____896, args) in
          (match uu____888 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____910)::(assertion,uu____912)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____938 =
                 let uu____940 =
                   unembed_tactic_0 FStar_Tactics_Embedding.unembed_unit
                     tactic in
                 let uu____942 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____940 uu____942 in
               (match uu____938 with
                | FStar_Tactics_Basic.Success (uu____946,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) -> (assertion, []))
           | uu____954 -> (t, []))
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
        let uu____994 =
          let uu____998 =
            let uu____999 = FStar_Syntax_Subst.compress t in
            uu____999.FStar_Syntax_Syntax.n in
          match uu____998 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1011 = traverse f e t1 in
              (match uu____1011 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1029 = traverse f e t1 in
              (match uu____1029 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1057 = traverse f e hd1 in
              (match uu____1057 with
               | (hd',gs1) ->
                   let uu____1068 =
                     FStar_List.fold_right
                       (fun uu____1083  ->
                          fun uu____1084  ->
                            match (uu____1083, uu____1084) with
                            | ((a,q),(as',gs)) ->
                                let uu____1127 = traverse f e a in
                                (match uu____1127 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1068 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1195 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1195 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1204 = traverse f e' topen in
                   (match uu____1204 with
                    | (topen',gs) ->
                        let uu____1215 =
                          let uu____1216 =
                            let uu____1231 =
                              FStar_Syntax_Subst.close bs1 topen' in
                            (bs1, uu____1231, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____1216 in
                        (uu____1215, gs)))
          | x -> (x, []) in
        match uu____994 with
        | (tn',gs) ->
            let t' =
              let uu___109_1251 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___109_1251.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___109_1251.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___109_1251.FStar_Syntax_Syntax.vars)
              } in
            let uu____1256 = f e t' in
            (match uu____1256 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      let initial = ((Prims.parse_int "1"), []) in
      let uu____1291 = traverse by_tactic_interp env goal in
      match uu____1291 with
      | (t',gs) ->
          let s = initial in
          let s1 =
            FStar_List.fold_left
              (fun uu____1319  ->
                 fun g  ->
                   match uu____1319 with
                   | (n1,gs1) ->
                       let gt' =
                         let uu____1340 =
                           let uu____1341 = FStar_Util.string_of_int n1 in
                           Prims.strcat "Goal #" uu____1341 in
                         FStar_TypeChecker_Util.label uu____1340
                           FStar_Range.dummyRange
                           g.FStar_Tactics_Basic.goal_ty in
                       ((n1 + (Prims.parse_int "1")),
                         (((g.FStar_Tactics_Basic.context), gt') :: gs1))) s
              gs in
          let uu____1347 = s1 in
          (match uu____1347 with | (uu____1356,gs1) -> (env, t') :: gs1)