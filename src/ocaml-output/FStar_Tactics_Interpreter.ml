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
  (let uu____169 = FStar_Ident.string_of_lid nm in
   let uu____170 = FStar_Syntax_Print.args_to_string args in
   FStar_Util.print2 "Reached %s, args are: %s\n" uu____169 uu____170);
  (match args with
   | a::[] ->
       let uu____185 =
         let uu____186 =
           let uu____187 = unembed_a (Prims.fst a) in f uu____187 in
         embed_b uu____186 in
       Some uu____185
   | uu____190 -> failwith "Unexpected interpretation of pure primitive")
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____233)::[] ->
      ((let uu____247 = FStar_Ident.string_of_lid nm in
        let uu____248 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.print2 "Reached %s, args are: %s\n" uu____247 uu____248);
       (let uu____249 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____249 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___104_258 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___104_258.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___104_258.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___104_258.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___104_258.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____261 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____261))
  | uu____262 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____322)::(embedded_state,uu____324)::[] ->
      ((let uu____346 = FStar_Ident.string_of_lid nm in
        let uu____347 = FStar_Syntax_Print.term_to_string embedded_state in
        FStar_Util.print2 "Reached %s, goals are: %s\n" uu____346 uu____347);
       (let uu____348 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____348 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___105_357 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___105_357.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___105_357.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___105_357.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___105_357.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____360 = let uu____362 = unembed_b b in t uu____362 in
              FStar_Tactics_Basic.run uu____360 ps1 in
            let uu____363 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____363))
  | uu____364 ->
      let uu____365 =
        let uu____366 = FStar_Ident.string_of_lid nm in
        let uu____367 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____366 uu____367 in
      failwith uu____365
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____444)::(b,uu____446)::(embedded_state,uu____448)::[] ->
      ((let uu____478 = FStar_Ident.string_of_lid nm in
        let uu____479 = FStar_Syntax_Print.term_to_string embedded_state in
        FStar_Util.print2 "Reached %s, goals are: %s\n" uu____478 uu____479);
       (let uu____480 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____480 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___106_489 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___106_489.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___106_489.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___106_489.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___106_489.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____492 =
                let uu____494 = unembed_a a in
                let uu____495 = unembed_b b in t uu____494 uu____495 in
              FStar_Tactics_Basic.run uu____492 ps1 in
            let uu____496 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            Some uu____496))
  | uu____497 ->
      let uu____498 =
        let uu____499 = FStar_Ident.string_of_lid nm in
        let uu____500 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____499 uu____500 in
      failwith uu____498
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____515)::(et2,uu____517)::(embedded_state,uu____519)::[] ->
            let uu____548 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____548 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___107_557 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___107_557.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___107_557.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___107_557.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___107_557.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____560 =
                     let uu____562 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____563 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____564 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____565 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____562 uu____563
                       uu____564 uu____565 in
                   FStar_Tactics_Basic.run uu____560 ps1 in
                 let uu____566 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____566)
        | uu____567 ->
            let uu____568 =
              let uu____569 = FStar_Ident.string_of_lid nm in
              let uu____570 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____569
                uu____570 in
            failwith uu____568
let rec primitive_steps:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  fun ps  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid nm in
      let uu____614 = interpretation nm1 in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = uu____614
      } in
    let uu____618 =
      mk1 "forall_intros_" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____619 =
      let uu____621 =
        mk1 "implies_intro_" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____622 =
        let uu____624 =
          mk1 "trivial_" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____625 =
          let uu____627 =
            mk1 "revert_" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____628 =
            let uu____630 =
              mk1 "clear_" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____631 =
              let uu____633 =
                mk1 "split_" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____634 =
                let uu____636 =
                  mk1 "merge_" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____637 =
                  let uu____639 =
                    mk1 "rewrite_" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____640 =
                    let uu____642 =
                      mk1 "smt_" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____643 =
                      let uu____645 =
                        mk1 "exact_" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____646 =
                        let uu____648 =
                          mk1 "apply_lemma_" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____649 =
                          let uu____651 =
                            mk1 "visit_" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____653 =
                            let uu____655 =
                              mk1 "focus_" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____657 =
                              let uu____659 =
                                mk1 "seq_" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____662 =
                                let uu____664 =
                                  mk1 "term_as_formula_"
                                    (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____666 =
                                  let uu____668 =
                                    mk1 "binders_of_env_"
                                      (Prims.parse_int "1")
                                      (binders_of_env ps) in
                                  let uu____669 =
                                    let uu____671 =
                                      mk1 "type_of_binder_"
                                        (Prims.parse_int "1") type_of_binder in
                                    let uu____672 =
                                      let uu____674 =
                                        mk1 "term_eq_" (Prims.parse_int "2")
                                          term_eq in
                                      let uu____675 =
                                        let uu____677 =
                                          mk1 "print_" (Prims.parse_int "2")
                                            (mk_tactic_interpretation_1 ps
                                               FStar_Tactics_Basic.print_proof_state
                                               FStar_Tactics_Embedding.unembed_string
                                               FStar_Tactics_Embedding.embed_unit
                                               FStar_TypeChecker_Common.t_unit) in
                                        let uu____678 =
                                          let uu____680 =
                                            mk1 "grewrite_"
                                              (Prims.parse_int "3")
                                              (grewrite_interpretation ps) in
                                          [uu____680] in
                                        uu____677 :: uu____678 in
                                      uu____674 :: uu____675 in
                                    uu____671 :: uu____672 in
                                  uu____668 :: uu____669 in
                                uu____664 :: uu____666 in
                              uu____659 :: uu____662 in
                            uu____655 :: uu____657 in
                          uu____651 :: uu____653 in
                        uu____648 :: uu____649 in
                      uu____645 :: uu____646 in
                    uu____642 :: uu____643 in
                  uu____639 :: uu____640 in
                uu____636 :: uu____637 in
              uu____633 :: uu____634 in
            uu____630 :: uu____631 in
          uu____627 :: uu____628 in
        uu____624 :: uu____625 in
      uu____621 :: uu____622 in
    uu____618 :: uu____619
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____689 =
           let uu____690 =
             let uu____691 =
               let uu____692 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____692 in
             [uu____691] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____690 in
         uu____689 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       (let uu____702 = FStar_Syntax_Print.term_to_string tm in
        FStar_Util.print1 "Starting normalizer with %s\n" uu____702);
       FStar_Options.set_option "debug_level"
         (FStar_Options.List [FStar_Options.String "Norm"]);
       (let result =
          let uu____705 = primitive_steps proof_state in
          FStar_TypeChecker_Normalize.normalize_with_primitive_steps
            uu____705 steps proof_state.FStar_Tactics_Basic.main_context tm in
        FStar_Options.set_option "debug_level" (FStar_Options.List []);
        (let uu____709 = FStar_Syntax_Print.term_to_string result in
         FStar_Util.print1 "Reduced tactic: got %s\n" uu____709);
        (let uu____710 =
           FStar_Tactics_Embedding.unembed_result
             proof_state.FStar_Tactics_Basic.main_context result unembed_b in
         match uu____710 with
         | FStar_Util.Inl (b,(goals,smt_goals)) ->
             FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
               (fun uu____737  ->
                  let uu____738 = FStar_Tactics_Basic.add_goals goals in
                  FStar_Tactics_Basic.bind uu____738
                    (fun uu____740  ->
                       let uu____741 =
                         FStar_Tactics_Basic.add_smt_goals smt_goals in
                       FStar_Tactics_Basic.bind uu____741
                         (fun uu____743  -> FStar_Tactics_Basic.ret b)))
         | FStar_Util.Inr (msg,(goals,smt_goals)) ->
             FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
               (fun uu____763  ->
                  let uu____764 = FStar_Tactics_Basic.add_goals goals in
                  FStar_Tactics_Basic.bind uu____764
                    (fun uu____766  ->
                       let uu____767 =
                         FStar_Tactics_Basic.add_smt_goals smt_goals in
                       FStar_Tactics_Basic.bind uu____767
                         (fun uu____769  -> FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____773 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____773 with
            | (hd1,args) ->
                let uu____800 =
                  let uu____808 =
                    let uu____809 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____809.FStar_Syntax_Syntax.n in
                  (uu____808, args) in
                (match uu____800 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____820)::(assertion,uu____822)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____848 =
                       let uu____850 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___108_852 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___108_852.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___108_852.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____850
                         (fun uu____853  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____848
                 | uu____854 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____875 = FStar_Syntax_Print.term_to_string goal in
       FStar_Util.print1 "About to preprocess %s\n" uu____875);
      (let p = FStar_Tactics_Basic.proofstate_of_goal_ty env goal in
       let uu____877 =
         let uu____879 = FStar_Tactics_Basic.visit evaluate_user_tactic in
         FStar_Tactics_Basic.run uu____879 p in
       match uu____877 with
       | FStar_Tactics_Basic.Success (uu____884,p2) ->
           let uu____886 =
             FStar_All.pipe_right p2.FStar_Tactics_Basic.goals
               (FStar_List.map
                  (fun g  ->
                     (let uu____898 = FStar_Tactics_Basic.goal_to_string g in
                      FStar_Util.print1 "Got goal: %s\n" uu____898);
                     ((g.FStar_Tactics_Basic.context),
                       (g.FStar_Tactics_Basic.goal_ty)))) in
           FStar_All.pipe_right p2.FStar_Tactics_Basic.smt_goals
             (FStar_List.map
                (fun g  ->
                   (let uu____907 = FStar_Tactics_Basic.goal_to_string g in
                    FStar_Util.print1 "Got SMT goal: %s\n" uu____907);
                   ((g.FStar_Tactics_Basic.context),
                     (g.FStar_Tactics_Basic.goal_ty))))
       | FStar_Tactics_Basic.Failed (msg,uu____909) ->
           (FStar_Util.print1 "Tactic failed: %s\n" msg;
            (let uu____912 =
               FStar_Tactics_Basic.goal_to_string
                 {
                   FStar_Tactics_Basic.context = env;
                   FStar_Tactics_Basic.witness = None;
                   FStar_Tactics_Basic.goal_ty = goal
                 } in
             FStar_Util.print1 "Got goal: %s\n" uu____912);
            [(env, goal)]))