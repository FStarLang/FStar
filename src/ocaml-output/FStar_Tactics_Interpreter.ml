open Prims
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____42)::[] ->
      ((let uu____56 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____56
        then
          let uu____59 = FStar_Ident.string_of_lid nm in
          let uu____60 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.print2 "Reached %s, args are: %s\n" uu____59 uu____60
        else ());
       (let uu____62 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____62 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_71 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_71.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_71.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_71.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___108_71.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____74 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____74))
  | uu____75 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____135)::(embedded_state,uu____137)::[] ->
      ((let uu____159 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____159
        then
          let uu____162 = FStar_Ident.string_of_lid nm in
          let uu____163 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____162 uu____163
        else ());
       (let uu____165 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____165 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_174 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_174.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_174.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_174.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___109_174.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____177 = let uu____179 = unembed_b b in t uu____179 in
              FStar_Tactics_Basic.run uu____177 ps1 in
            let uu____180 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____180))
  | uu____181 ->
      let uu____182 =
        let uu____183 = FStar_Ident.string_of_lid nm in
        let uu____184 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____183 uu____184 in
      failwith uu____182
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____261)::(b,uu____263)::(embedded_state,uu____265)::[] ->
      ((let uu____295 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____295
        then
          let uu____298 = FStar_Ident.string_of_lid nm in
          let uu____299 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____298 uu____299
        else ());
       (let uu____301 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____301 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_310 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_310.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_310.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_310.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___110_310.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____313 =
                let uu____315 = unembed_a a in
                let uu____316 = unembed_b b in t uu____315 uu____316 in
              FStar_Tactics_Basic.run uu____313 ps1 in
            let uu____317 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            Some uu____317))
  | uu____318 ->
      let uu____319 =
        let uu____320 = FStar_Ident.string_of_lid nm in
        let uu____321 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____320 uu____321 in
      failwith uu____319
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____336)::(et2,uu____338)::(embedded_state,uu____340)::[] ->
            let uu____369 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____369 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___111_378 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___111_378.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___111_378.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___111_378.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___111_378.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____381 =
                     let uu____383 =
                       FStar_Reflection_Basic.type_of_embedded et1 in
                     let uu____384 =
                       FStar_Reflection_Basic.type_of_embedded et2 in
                     let uu____385 = FStar_Reflection_Basic.unembed_term et1 in
                     let uu____386 = FStar_Reflection_Basic.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____383 uu____384
                       uu____385 uu____386 in
                   FStar_Tactics_Basic.run uu____381 ps1 in
                 let uu____387 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Reflection_Basic.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____387)
        | uu____388 ->
            let uu____389 =
              let uu____390 = FStar_Ident.string_of_lid nm in
              let uu____391 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____390
                uu____391 in
            failwith uu____389
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
    let uu____437 =
      mk1 "__forall_intros" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Reflection_Basic.embed_binders
           FStar_Reflection_Data.fstar_refl_binders) in
    let uu____438 =
      let uu____440 =
        mk1 "__implies_intro" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Reflection_Basic.embed_binder
             FStar_Reflection_Data.fstar_refl_binder) in
      let uu____441 =
        let uu____443 =
          mk1 "__trivial" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Reflection_Basic.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____444 =
          let uu____446 =
            mk1 "__revert" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Reflection_Basic.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____447 =
            let uu____449 =
              mk1 "__clear" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Reflection_Basic.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____450 =
              let uu____452 =
                mk1 "__split" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Reflection_Basic.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____453 =
                let uu____455 =
                  mk1 "__merge" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Reflection_Basic.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____456 =
                  let uu____458 =
                    mk1 "__rewrite" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Reflection_Basic.unembed_binder
                         FStar_Reflection_Basic.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____459 =
                    let uu____461 =
                      mk1 "__smt" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Reflection_Basic.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____462 =
                      let uu____464 =
                        mk1 "__exact" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Reflection_Basic.unembed_term
                             FStar_Reflection_Basic.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____465 =
                        let uu____467 =
                          mk1 "__apply_lemma" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Reflection_Basic.unembed_term
                               FStar_Reflection_Basic.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____468 =
                          let uu____470 =
                            mk1 "__visit" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Reflection_Basic.unembed_unit)
                                 FStar_Reflection_Basic.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____472 =
                            let uu____474 =
                              mk1 "__focus" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   FStar_Tactics_Basic.focus_cur_goal
                                   (unembed_tactic_0
                                      FStar_Reflection_Basic.unembed_unit)
                                   FStar_Reflection_Basic.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____476 =
                              let uu____478 =
                                mk1 "__seq" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Reflection_Basic.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Reflection_Basic.unembed_unit)
                                     FStar_Reflection_Basic.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____481 =
                                let uu____483 =
                                  mk1 "__print" (Prims.parse_int "2")
                                    (mk_tactic_interpretation_1 ps
                                       (fun x  ->
                                          FStar_Tactics_Basic.tacprint x;
                                          FStar_Tactics_Basic.ret ())
                                       FStar_Reflection_Basic.unembed_string
                                       FStar_Reflection_Basic.embed_unit
                                       FStar_TypeChecker_Common.t_unit) in
                                let uu____486 =
                                  let uu____488 =
                                    mk1 "__dump" (Prims.parse_int "2")
                                      (mk_tactic_interpretation_1 ps
                                         FStar_Tactics_Basic.print_proof_state
                                         FStar_Reflection_Basic.unembed_string
                                         FStar_Reflection_Basic.embed_unit
                                         FStar_TypeChecker_Common.t_unit) in
                                  let uu____489 =
                                    let uu____491 =
                                      mk1 "__grewrite" (Prims.parse_int "3")
                                        (grewrite_interpretation ps) in
                                    [uu____491] in
                                  uu____488 :: uu____489 in
                                uu____483 :: uu____486 in
                              uu____478 :: uu____481 in
                            uu____474 :: uu____476 in
                          uu____470 :: uu____472 in
                        uu____467 :: uu____468 in
                      uu____464 :: uu____465 in
                    uu____461 :: uu____462 in
                  uu____458 :: uu____459 in
                uu____455 :: uu____456 in
              uu____452 :: uu____453 in
            uu____449 :: uu____450 in
          uu____446 :: uu____447 in
        uu____443 :: uu____444 in
      uu____440 :: uu____441 in
    uu____437 :: uu____438
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____500 =
           let uu____501 =
             let uu____502 =
               let uu____503 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____503 in
             [uu____502] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____501 in
         uu____500 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____512 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____517  ->
              let uu____518 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____518) in
       FStar_Tactics_Basic.bind uu____512
         (fun uu____519  ->
            let result =
              let uu____521 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____521 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____523 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____528  ->
                   let uu____529 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____529) in
            FStar_Tactics_Basic.bind uu____523
              (fun uu____530  ->
                 let uu____531 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____531 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____558  ->
                          let uu____559 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____559
                            (fun uu____561  ->
                               let uu____562 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____562
                                 (fun uu____564  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____584  ->
                          let uu____585 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____585
                            (fun uu____587  ->
                               let uu____588 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____588
                                 (fun uu____590  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____594 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____594 with
            | (hd1,args) ->
                let uu____621 =
                  let uu____629 =
                    let uu____630 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____630.FStar_Syntax_Syntax.n in
                  (uu____629, args) in
                (match uu____621 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____641)::(assertion,uu____643)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____669 =
                       let uu____671 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___112_673 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___112_673.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___112_673.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____671
                         (fun uu____674  ->
                            unembed_tactic_0
                              FStar_Reflection_Basic.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal uu____669
                 | uu____675 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____695 = FStar_Syntax_Util.head_and_args t in
      match uu____695 with
      | (hd1,args) ->
          let uu____724 =
            let uu____732 =
              let uu____733 = FStar_Syntax_Util.un_uinst hd1 in
              uu____733.FStar_Syntax_Syntax.n in
            (uu____732, args) in
          (match uu____724 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____746)::(assertion,uu____748)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____774 =
                 let uu____776 =
                   unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                     tactic in
                 let uu____778 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____776 uu____778 in
               (match uu____774 with
                | FStar_Tactics_Basic.Success (uu____782,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____790 -> (t, []))
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
        let uu____830 =
          let uu____834 =
            let uu____835 = FStar_Syntax_Subst.compress t in
            uu____835.FStar_Syntax_Syntax.n in
          match uu____834 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____847 = traverse f e t1 in
              (match uu____847 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____865 = traverse f e t1 in
              (match uu____865 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____878;
                 FStar_Syntax_Syntax.pos = uu____879;
                 FStar_Syntax_Syntax.vars = uu____880;_},(p,uu____882)::
               (q,uu____884)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____915 =
                let uu____919 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____919 q in
              (match uu____915 with
               | (q',gs) ->
                   let uu____927 =
                     let uu____928 = FStar_Syntax_Util.mk_imp p q' in
                     uu____928.FStar_Syntax_Syntax.n in
                   (uu____927, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____948 = traverse f e hd1 in
              (match uu____948 with
               | (hd',gs1) ->
                   let uu____959 =
                     FStar_List.fold_right
                       (fun uu____974  ->
                          fun uu____975  ->
                            match (uu____974, uu____975) with
                            | ((a,q),(as',gs)) ->
                                let uu____1018 = traverse f e a in
                                (match uu____1018 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____959 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1086 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1086 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1095 = traverse f e' topen in
                   (match uu____1095 with
                    | (topen',gs) ->
                        let uu____1106 =
                          let uu____1107 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1107.FStar_Syntax_Syntax.n in
                        (uu____1106, gs)))
          | x -> (x, []) in
        match uu____830 with
        | (tn',gs) ->
            let t' =
              let uu___113_1123 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___113_1123.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___113_1123.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___113_1123.FStar_Syntax_Syntax.vars)
              } in
            let uu____1128 = f e t' in
            (match uu____1128 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1153 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1153);
      (let uu____1157 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1157
       then
         let uu____1160 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1160
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1173 = traverse by_tactic_interp env goal in
       match uu____1173 with
       | (t',gs) ->
           ((let uu____1185 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1185
             then
               let uu____1188 =
                 let uu____1189 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1189
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1190 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1188 uu____1190
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1209  ->
                    fun g  ->
                      match uu____1209 with
                      | (n1,gs1) ->
                          ((let uu____1230 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1230
                            then
                              let uu____1233 = FStar_Util.string_of_int n1 in
                              let uu____1234 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1233 uu____1234
                            else ());
                           (let gt' =
                              let uu____1237 =
                                let uu____1238 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1238 in
                              FStar_TypeChecker_Util.label uu____1237
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1244 = s1 in
             match uu____1244 with | (uu____1253,gs1) -> (env, t') :: gs1)))