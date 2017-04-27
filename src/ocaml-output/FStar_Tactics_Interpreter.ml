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
  (let uu____202 = FStar_Ident.string_of_lid nm in
   let uu____203 = FStar_Syntax_Print.args_to_string args in
   FStar_Util.print2 "Reached %s, args are: %s\n" uu____202 uu____203);
  (match args with
   | a::[] ->
       let uu____218 =
         let uu____219 =
           let uu____220 = unembed_a (Prims.fst a) in f uu____220 in
         embed_b uu____219 in
       Some uu____218
   | uu____223 -> failwith "Unexpected interpretation of pure primitive")
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____266)::[] ->
      ((let uu____280 = FStar_Ident.string_of_lid nm in
        let uu____281 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.print2 "Reached %s, args are: %s\n" uu____280 uu____281);
       (let uu____282 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____282 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___101_291 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___101_291.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___101_291.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___101_291.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___101_291.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____294 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____294))
  | uu____295 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____355)::(embedded_state,uu____357)::[] ->
      ((let uu____379 = FStar_Ident.string_of_lid nm in
        let uu____380 = FStar_Syntax_Print.term_to_string embedded_state in
        FStar_Util.print2 "Reached %s, goals are: %s\n" uu____379 uu____380);
       (let uu____381 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____381 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___102_390 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___102_390.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___102_390.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___102_390.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___102_390.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____393 = let uu____395 = unembed_b b in t uu____395 in
              FStar_Tactics_Basic.run uu____393 ps1 in
            let uu____396 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____396))
  | uu____397 ->
      let uu____398 =
        let uu____399 = FStar_Ident.string_of_lid nm in
        let uu____400 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____399 uu____400 in
      failwith uu____398
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____477)::(b,uu____479)::(embedded_state,uu____481)::[] ->
      ((let uu____511 = FStar_Ident.string_of_lid nm in
        let uu____512 = FStar_Syntax_Print.term_to_string embedded_state in
        FStar_Util.print2 "Reached %s, goals are: %s\n" uu____511 uu____512);
       (let uu____513 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____513 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___103_522 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___103_522.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___103_522.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___103_522.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___103_522.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____525 =
                let uu____527 = unembed_a a in
                let uu____528 = unembed_b b in t uu____527 uu____528 in
              FStar_Tactics_Basic.run uu____525 ps1 in
            let uu____529 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            Some uu____529))
  | uu____530 ->
      let uu____531 =
        let uu____532 = FStar_Ident.string_of_lid nm in
        let uu____533 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____532 uu____533 in
      failwith uu____531
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
    let uu____579 =
      mk1 "forall_intros_" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____580 =
      let uu____582 =
        mk1 "implies_intro_" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____583 =
        let uu____585 =
          mk1 "trivial_" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____586 =
          let uu____588 =
            mk1 "revert_" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____589 =
            let uu____591 =
              mk1 "clear_" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____592 =
              let uu____594 =
                mk1 "split_" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____595 =
                let uu____597 =
                  mk1 "merge_" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____598 =
                  let uu____600 =
                    mk1 "rewrite_" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____601 =
                    let uu____603 =
                      mk1 "smt_" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____604 =
                      let uu____606 =
                        mk1 "exact_" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____607 =
                        let uu____609 =
                          mk1 "apply_lemma_" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____610 =
                          let uu____612 =
                            mk1 "visit_" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____614 =
                            let uu____616 =
                              mk1 "focus_" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____618 =
                              let uu____620 =
                                mk1 "seq_" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____623 =
                                let uu____625 =
                                  mk1 "term_as_formula" (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____627 =
                                  let uu____629 =
                                    mk1 "quote" (Prims.parse_int "2") quote in
                                  let uu____630 =
                                    let uu____632 =
                                      mk1 "binders_of_env"
                                        (Prims.parse_int "1")
                                        (binders_of_env ps) in
                                    let uu____633 =
                                      let uu____635 =
                                        mk1 "type_of_binder"
                                          (Prims.parse_int "1")
                                          type_of_binder in
                                      let uu____636 =
                                        let uu____638 =
                                          mk1 "term_eq" (Prims.parse_int "2")
                                            term_eq in
                                        [uu____638] in
                                      uu____635 :: uu____636 in
                                    uu____632 :: uu____633 in
                                  uu____629 :: uu____630 in
                                uu____625 :: uu____627 in
                              uu____620 :: uu____623 in
                            uu____616 :: uu____618 in
                          uu____612 :: uu____614 in
                        uu____609 :: uu____610 in
                      uu____606 :: uu____607 in
                    uu____603 :: uu____604 in
                  uu____600 :: uu____601 in
                uu____597 :: uu____598 in
              uu____594 :: uu____595 in
            uu____591 :: uu____592 in
          uu____588 :: uu____589 in
        uu____585 :: uu____586 in
      uu____582 :: uu____583 in
    uu____579 :: uu____580
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____647 =
           let uu____648 =
             let uu____649 =
               let uu____650 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____650 in
             [uu____649] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____648 in
         uu____647 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       (let uu____660 = FStar_Syntax_Print.term_to_string tm in
        FStar_Util.print1 "Starting normalizer with %s\n" uu____660);
       FStar_Options.set_option "debug_level"
         (FStar_Options.List [FStar_Options.String "Norm"]);
       (let result =
          let uu____663 = primitive_steps proof_state in
          FStar_TypeChecker_Normalize.normalize_with_primitive_steps
            uu____663 steps proof_state.FStar_Tactics_Basic.main_context tm in
        FStar_Options.set_option "debug_level" (FStar_Options.List []);
        (let uu____667 = FStar_Syntax_Print.term_to_string result in
         FStar_Util.print1 "Reduced tactic: got %s\n" uu____667);
        (let uu____668 =
           FStar_Tactics_Embedding.unembed_result
             proof_state.FStar_Tactics_Basic.main_context result unembed_b in
         match uu____668 with
         | FStar_Util.Inl (b,(goals,smt_goals)) ->
             FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
               (fun uu____695  ->
                  let uu____696 = FStar_Tactics_Basic.add_goals goals in
                  FStar_Tactics_Basic.bind uu____696
                    (fun uu____698  ->
                       let uu____699 =
                         FStar_Tactics_Basic.add_smt_goals smt_goals in
                       FStar_Tactics_Basic.bind uu____699
                         (fun uu____701  -> FStar_Tactics_Basic.ret b)))
         | FStar_Util.Inr (msg,(goals,smt_goals)) ->
             FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
               (fun uu____721  ->
                  let uu____722 = FStar_Tactics_Basic.add_goals goals in
                  FStar_Tactics_Basic.bind uu____722
                    (fun uu____724  ->
                       let uu____725 =
                         FStar_Tactics_Basic.add_smt_goals smt_goals in
                       FStar_Tactics_Basic.bind uu____725
                         (fun uu____727  -> FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____731 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____731 with
            | (hd1,args) ->
                let uu____758 =
                  let uu____766 =
                    let uu____767 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____767.FStar_Syntax_Syntax.n in
                  (uu____766, args) in
                (match uu____758 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____778)::(assertion,uu____780)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____806 =
                       let uu____808 =
                         FStar_Tactics_Basic.replace
                           (let uu___104_810 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___104_810.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___104_810.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____808
                         (fun uu____811  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____806
                 | uu____812 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      let uu____832 =
        (let uu____833 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals uu____833 FStar_Syntax_Const.prims_lid) ||
          (let uu____834 =
             let uu____835 = FStar_TypeChecker_Env.current_module env in
             FStar_Ident.string_of_lid uu____835 in
           FStar_Util.starts_with uu____834 "FStar.") in
      if uu____832
      then [(env, goal)]
      else
        ((let uu____845 = FStar_Syntax_Print.term_to_string goal in
          FStar_Util.print1 "About to preprocess %s\n" uu____845);
         (let p = FStar_Tactics_Basic.proofstate_of_goal_ty env goal in
          let uu____847 =
            let uu____849 = FStar_Tactics_Basic.visit evaluate_user_tactic in
            FStar_Tactics_Basic.run uu____849 p in
          match uu____847 with
          | FStar_Tactics_Basic.Success (uu____854,p2) ->
              FStar_All.pipe_right
                (FStar_List.append p2.FStar_Tactics_Basic.goals
                   p2.FStar_Tactics_Basic.smt_goals)
                (FStar_List.map
                   (fun g  ->
                      (let uu____864 = FStar_Tactics_Basic.goal_to_string g in
                       FStar_Util.print1 "Got goal: %s\n" uu____864);
                      ((g.FStar_Tactics_Basic.context),
                        (g.FStar_Tactics_Basic.goal_ty))))
          | FStar_Tactics_Basic.Failed (msg,uu____866) ->
              (FStar_Util.print1 "Tactic failed: %s\n" msg;
               (let uu____869 =
                  FStar_Tactics_Basic.goal_to_string
                    {
                      FStar_Tactics_Basic.context = env;
                      FStar_Tactics_Basic.witness = None;
                      FStar_Tactics_Basic.goal_ty = goal
                    } in
                FStar_Util.print1 "Got goal: %s\n" uu____869);
               [(env, goal)])))