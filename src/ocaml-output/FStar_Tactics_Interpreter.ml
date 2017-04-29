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
          let uu____150 = FStar_Syntax_Util.eq_tm t1 t2 in
          (match uu____150 with
           | FStar_Syntax_Util.Equal  ->
               let uu____152 = FStar_Tactics_Embedding.embed_bool true in
               Some uu____152
           | uu____153 ->
               let uu____154 = FStar_Tactics_Embedding.embed_bool false in
               Some uu____154)
      | uu____155 -> None
let mk_pure_interpretation_1 f unembed_a embed_b nm args =
  (let uu____202 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____202
   then
     let uu____205 = FStar_Ident.string_of_lid nm in
     let uu____206 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____205 uu____206
   else ());
  (match args with
   | a::[] ->
       let uu____222 =
         let uu____223 =
           let uu____224 = unembed_a (Prims.fst a) in f uu____224 in
         embed_b uu____223 in
       Some uu____222
   | uu____227 -> failwith "Unexpected interpretation of pure primitive")
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____270)::[] ->
      ((let uu____284 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____284
        then
          let uu____287 = FStar_Ident.string_of_lid nm in
          let uu____288 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.print2 "Reached %s, args are: %s\n" uu____287 uu____288
        else ());
       (let uu____290 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____290 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_299 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_299.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_299.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_299.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___108_299.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____302 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____302))
  | uu____303 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____363)::(embedded_state,uu____365)::[] ->
      ((let uu____387 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____387
        then
          let uu____390 = FStar_Ident.string_of_lid nm in
          let uu____391 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____390 uu____391
        else ());
       (let uu____393 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____393 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_402 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_402.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_402.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_402.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___109_402.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____405 = let uu____407 = unembed_b b in t uu____407 in
              FStar_Tactics_Basic.run uu____405 ps1 in
            let uu____408 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____408))
  | uu____409 ->
      let uu____410 =
        let uu____411 = FStar_Ident.string_of_lid nm in
        let uu____412 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____411 uu____412 in
      failwith uu____410
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____489)::(b,uu____491)::(embedded_state,uu____493)::[] ->
      ((let uu____523 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____523
        then
          let uu____526 = FStar_Ident.string_of_lid nm in
          let uu____527 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____526 uu____527
        else ());
       (let uu____529 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____529 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_538 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_538.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_538.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_538.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___110_538.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____541 =
                let uu____543 = unembed_a a in
                let uu____544 = unembed_b b in t uu____543 uu____544 in
              FStar_Tactics_Basic.run uu____541 ps1 in
            let uu____545 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            Some uu____545))
  | uu____546 ->
      let uu____547 =
        let uu____548 = FStar_Ident.string_of_lid nm in
        let uu____549 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____548 uu____549 in
      failwith uu____547
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____564)::(et2,uu____566)::(embedded_state,uu____568)::[] ->
            let uu____597 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____597 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___111_606 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___111_606.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___111_606.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___111_606.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___111_606.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____609 =
                     let uu____611 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____612 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____613 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____614 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____611 uu____612
                       uu____613 uu____614 in
                   FStar_Tactics_Basic.run uu____609 ps1 in
                 let uu____615 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____615)
        | uu____616 ->
            let uu____617 =
              let uu____618 = FStar_Ident.string_of_lid nm in
              let uu____619 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____618
                uu____619 in
            failwith uu____617
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
    let uu____665 =
      mk1 "forall_intros_" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____666 =
      let uu____668 =
        mk1 "implies_intro_" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____669 =
        let uu____671 =
          mk1 "trivial_" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____672 =
          let uu____674 =
            mk1 "revert_" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____675 =
            let uu____677 =
              mk1 "clear_" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____678 =
              let uu____680 =
                mk1 "split_" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____681 =
                let uu____683 =
                  mk1 "merge_" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____684 =
                  let uu____686 =
                    mk1 "rewrite_" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____687 =
                    let uu____689 =
                      mk1 "smt_" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____690 =
                      let uu____692 =
                        mk1 "exact_" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____693 =
                        let uu____695 =
                          mk1 "apply_lemma_" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____696 =
                          let uu____698 =
                            mk1 "visit_" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____700 =
                            let uu____702 =
                              mk1 "focus_" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____704 =
                              let uu____706 =
                                mk1 "seq_" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____709 =
                                let uu____711 =
                                  mk1 "term_as_formula_"
                                    (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____713 =
                                  let uu____715 =
                                    mk1 "inspect_" (Prims.parse_int "1")
                                      (mk_pure_interpretation_1
                                         FStar_Tactics_Embedding.inspect
                                         FStar_Tactics_Embedding.unembed_term
                                         (FStar_Tactics_Embedding.embed_option
                                            FStar_Tactics_Embedding.embed_term_view
                                            FStar_Tactics_Embedding.fstar_tactics_term_view)) in
                                  let uu____717 =
                                    let uu____719 =
                                      mk1 "binders_of_env_"
                                        (Prims.parse_int "1")
                                        (binders_of_env ps) in
                                    let uu____720 =
                                      let uu____722 =
                                        mk1 "type_of_binder_"
                                          (Prims.parse_int "1")
                                          type_of_binder in
                                      let uu____723 =
                                        let uu____725 =
                                          mk1 "term_eq_"
                                            (Prims.parse_int "2") term_eq in
                                        let uu____726 =
                                          let uu____728 =
                                            mk1 "print_"
                                              (Prims.parse_int "2")
                                              (mk_tactic_interpretation_1 ps
                                                 FStar_Tactics_Basic.print_proof_state
                                                 FStar_Tactics_Embedding.unembed_string
                                                 FStar_Tactics_Embedding.embed_unit
                                                 FStar_TypeChecker_Common.t_unit) in
                                          let uu____729 =
                                            let uu____731 =
                                              mk1 "grewrite_"
                                                (Prims.parse_int "3")
                                                (grewrite_interpretation ps) in
                                            [uu____731] in
                                          uu____728 :: uu____729 in
                                        uu____725 :: uu____726 in
                                      uu____722 :: uu____723 in
                                    uu____719 :: uu____720 in
                                  uu____715 :: uu____717 in
                                uu____711 :: uu____713 in
                              uu____706 :: uu____709 in
                            uu____702 :: uu____704 in
                          uu____698 :: uu____700 in
                        uu____695 :: uu____696 in
                      uu____692 :: uu____693 in
                    uu____689 :: uu____690 in
                  uu____686 :: uu____687 in
                uu____683 :: uu____684 in
              uu____680 :: uu____681 in
            uu____677 :: uu____678 in
          uu____674 :: uu____675 in
        uu____671 :: uu____672 in
      uu____668 :: uu____669 in
    uu____665 :: uu____666
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____740 =
           let uu____741 =
             let uu____742 =
               let uu____743 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____743 in
             [uu____742] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____741 in
         uu____740 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____752 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____757  ->
              let uu____758 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____758) in
       FStar_Tactics_Basic.bind uu____752
         (fun uu____759  ->
            let result =
              let uu____761 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____761 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____763 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____768  ->
                   let uu____769 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____769) in
            FStar_Tactics_Basic.bind uu____763
              (fun uu____770  ->
                 let uu____771 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____771 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____798  ->
                          let uu____799 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____799
                            (fun uu____801  ->
                               let uu____802 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____802
                                 (fun uu____804  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____824  ->
                          let uu____825 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____825
                            (fun uu____827  ->
                               let uu____828 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____828
                                 (fun uu____830  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____834 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____834 with
            | (hd1,args) ->
                let uu____861 =
                  let uu____869 =
                    let uu____870 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____870.FStar_Syntax_Syntax.n in
                  (uu____869, args) in
                (match uu____861 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____881)::(assertion,uu____883)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____909 =
                       let uu____911 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___112_913 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___112_913.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___112_913.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____911
                         (fun uu____914  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____909
                 | uu____915 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____935 = FStar_Syntax_Util.head_and_args t in
      match uu____935 with
      | (hd1,args) ->
          let uu____964 =
            let uu____972 =
              let uu____973 = FStar_Syntax_Util.un_uinst hd1 in
              uu____973.FStar_Syntax_Syntax.n in
            (uu____972, args) in
          (match uu____964 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____986)::(assertion,uu____988)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____1014 =
                 let uu____1016 =
                   unembed_tactic_0 FStar_Tactics_Embedding.unembed_unit
                     tactic in
                 let uu____1018 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____1016 uu____1018 in
               (match uu____1014 with
                | FStar_Tactics_Basic.Success (uu____1022,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____1030 -> (t, []))
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
        let uu____1070 =
          let uu____1074 =
            let uu____1075 = FStar_Syntax_Subst.compress t in
            uu____1075.FStar_Syntax_Syntax.n in
          match uu____1074 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1087 = traverse f e t1 in
              (match uu____1087 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1105 = traverse f e t1 in
              (match uu____1105 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1118;
                 FStar_Syntax_Syntax.pos = uu____1119;
                 FStar_Syntax_Syntax.vars = uu____1120;_},(p,uu____1122)::
               (q,uu____1124)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1155 =
                let uu____1159 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1159 q in
              (match uu____1155 with
               | (q',gs) ->
                   let uu____1167 =
                     let uu____1168 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1168.FStar_Syntax_Syntax.n in
                   (uu____1167, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1188 = traverse f e hd1 in
              (match uu____1188 with
               | (hd',gs1) ->
                   let uu____1199 =
                     FStar_List.fold_right
                       (fun uu____1214  ->
                          fun uu____1215  ->
                            match (uu____1214, uu____1215) with
                            | ((a,q),(as',gs)) ->
                                let uu____1258 = traverse f e a in
                                (match uu____1258 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1199 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1326 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1326 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1335 = traverse f e' topen in
                   (match uu____1335 with
                    | (topen',gs) ->
                        let uu____1346 =
                          let uu____1347 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1347.FStar_Syntax_Syntax.n in
                        (uu____1346, gs)))
          | x -> (x, []) in
        match uu____1070 with
        | (tn',gs) ->
            let t' =
              let uu___113_1363 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___113_1363.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___113_1363.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___113_1363.FStar_Syntax_Syntax.vars)
              } in
            let uu____1368 = f e t' in
            (match uu____1368 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1393 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1393);
      (let uu____1397 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1397
       then
         let uu____1400 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1400
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1413 = traverse by_tactic_interp env goal in
       match uu____1413 with
       | (t',gs) ->
           ((let uu____1425 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1425
             then
               let uu____1428 =
                 let uu____1429 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1429
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1430 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1428 uu____1430
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1449  ->
                    fun g  ->
                      match uu____1449 with
                      | (n1,gs1) ->
                          ((let uu____1470 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1470
                            then
                              let uu____1473 = FStar_Util.string_of_int n1 in
                              let uu____1474 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1473 uu____1474
                            else ());
                           (let gt' =
                              let uu____1477 =
                                let uu____1478 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1478 in
                              FStar_TypeChecker_Util.label uu____1477
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1484 = s1 in
             match uu____1484 with | (uu____1493,gs1) -> (env, t') :: gs1)))