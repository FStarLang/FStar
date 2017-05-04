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
    let mk_refl nm arity interpretation =
      let nm1 = FStar_Reflection_Data.fstar_refl_lid nm in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      } in
    let binders_of_env_int nm args =
      match args with
      | (e,uu____481)::[] ->
          let uu____486 =
            let uu____487 =
              let uu____489 =
                FStar_Tactics_Embedding.unembed_env
                  ps.FStar_Tactics_Basic.main_context e in
              FStar_TypeChecker_Env.all_binders uu____489 in
            FStar_Reflection_Basic.embed_binders uu____487 in
          Some uu____486
      | uu____490 ->
          let uu____494 =
            let uu____495 = FStar_Ident.string_of_lid nm in
            let uu____496 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____495
              uu____496 in
          failwith uu____494 in
    let uu____498 =
      let uu____500 =
        mk1 "__forall_intros" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
             FStar_Reflection_Basic.embed_binders
             FStar_Reflection_Data.fstar_refl_binders) in
      let uu____501 =
        let uu____503 =
          mk1 "__implies_intro" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
               FStar_Reflection_Basic.embed_binder
               FStar_Reflection_Data.fstar_refl_binder) in
        let uu____504 =
          let uu____506 =
            mk1 "__trivial" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
                 FStar_Reflection_Basic.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____507 =
            let uu____509 =
              mk1 "__revert" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                   FStar_Reflection_Basic.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____510 =
              let uu____512 =
                mk1 "__clear" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                     FStar_Reflection_Basic.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____513 =
                let uu____515 =
                  mk1 "__split" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                       FStar_Reflection_Basic.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____516 =
                  let uu____518 =
                    mk1 "__merge" (Prims.parse_int "1")
                      (mk_tactic_interpretation_0 ps
                         FStar_Tactics_Basic.merge_sub_goals
                         FStar_Reflection_Basic.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____519 =
                    let uu____521 =
                      mk1 "__rewrite" (Prims.parse_int "2")
                        (mk_tactic_interpretation_1 ps
                           FStar_Tactics_Basic.rewrite
                           FStar_Reflection_Basic.unembed_binder
                           FStar_Reflection_Basic.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____522 =
                      let uu____524 =
                        mk1 "__smt" (Prims.parse_int "1")
                          (mk_tactic_interpretation_0 ps
                             FStar_Tactics_Basic.smt
                             FStar_Reflection_Basic.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____525 =
                        let uu____527 =
                          mk1 "__exact" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.exact
                               FStar_Reflection_Basic.unembed_term
                               FStar_Reflection_Basic.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____528 =
                          let uu____530 =
                            mk1 "__apply_lemma" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.apply_lemma
                                 FStar_Reflection_Basic.unembed_term
                                 FStar_Reflection_Basic.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____531 =
                            let uu____533 =
                              mk1 "__visit" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   FStar_Tactics_Basic.visit
                                   (unembed_tactic_0
                                      FStar_Reflection_Basic.unembed_unit)
                                   FStar_Reflection_Basic.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____535 =
                              let uu____537 =
                                mk1 "__focus" (Prims.parse_int "2")
                                  (mk_tactic_interpretation_1 ps
                                     FStar_Tactics_Basic.focus_cur_goal
                                     (unembed_tactic_0
                                        FStar_Reflection_Basic.unembed_unit)
                                     FStar_Reflection_Basic.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____539 =
                                let uu____541 =
                                  mk1 "__seq" (Prims.parse_int "3")
                                    (mk_tactic_interpretation_2 ps
                                       FStar_Tactics_Basic.seq
                                       (unembed_tactic_0
                                          FStar_Reflection_Basic.unembed_unit)
                                       (unembed_tactic_0
                                          FStar_Reflection_Basic.unembed_unit)
                                       FStar_Reflection_Basic.embed_unit
                                       FStar_TypeChecker_Common.t_unit) in
                                let uu____544 =
                                  let uu____546 =
                                    mk_refl ["Syntax"; "__binders_of_env"]
                                      (Prims.parse_int "1")
                                      binders_of_env_int in
                                  let uu____547 =
                                    let uu____549 =
                                      mk1 "__print" (Prims.parse_int "2")
                                        (mk_tactic_interpretation_1 ps
                                           (fun x  ->
                                              FStar_Tactics_Basic.tacprint x;
                                              FStar_Tactics_Basic.ret ())
                                           FStar_Reflection_Basic.unembed_string
                                           FStar_Reflection_Basic.embed_unit
                                           FStar_TypeChecker_Common.t_unit) in
                                    let uu____552 =
                                      let uu____554 =
                                        mk1 "__dump" (Prims.parse_int "2")
                                          (mk_tactic_interpretation_1 ps
                                             FStar_Tactics_Basic.print_proof_state
                                             FStar_Reflection_Basic.unembed_string
                                             FStar_Reflection_Basic.embed_unit
                                             FStar_TypeChecker_Common.t_unit) in
                                      let uu____555 =
                                        let uu____557 =
                                          mk1 "__grewrite"
                                            (Prims.parse_int "3")
                                            (grewrite_interpretation ps) in
                                        [uu____557] in
                                      uu____554 :: uu____555 in
                                    uu____549 :: uu____552 in
                                  uu____546 :: uu____547 in
                                uu____541 :: uu____544 in
                              uu____537 :: uu____539 in
                            uu____533 :: uu____535 in
                          uu____530 :: uu____531 in
                        uu____527 :: uu____528 in
                      uu____524 :: uu____525 in
                    uu____521 :: uu____522 in
                  uu____518 :: uu____519 in
                uu____515 :: uu____516 in
              uu____512 :: uu____513 in
            uu____509 :: uu____510 in
          uu____506 :: uu____507 in
        uu____503 :: uu____504 in
      uu____500 :: uu____501 in
    FStar_List.append uu____498
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____566 =
           let uu____567 =
             let uu____568 =
               let uu____569 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____569 in
             [uu____568] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____567 in
         uu____566 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____578 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____583  ->
              let uu____584 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____584) in
       FStar_Tactics_Basic.bind uu____578
         (fun uu____585  ->
            let result =
              let uu____587 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____587 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____589 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____594  ->
                   let uu____595 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____595) in
            FStar_Tactics_Basic.bind uu____589
              (fun uu____596  ->
                 let uu____597 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____597 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____624  ->
                          let uu____625 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____625
                            (fun uu____627  ->
                               let uu____628 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____628
                                 (fun uu____630  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____650  ->
                          let uu____651 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____651
                            (fun uu____653  ->
                               let uu____654 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____654
                                 (fun uu____656  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____660 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____660 with
            | (hd1,args) ->
                let uu____687 =
                  let uu____695 =
                    let uu____696 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____696.FStar_Syntax_Syntax.n in
                  (uu____695, args) in
                (match uu____687 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____707)::(assertion,uu____709)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____735 =
                       let uu____737 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___112_739 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___112_739.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___112_739.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____737
                         (fun uu____740  ->
                            unembed_tactic_0
                              FStar_Reflection_Basic.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal uu____735
                 | uu____741 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____761 = FStar_Syntax_Util.head_and_args t in
      match uu____761 with
      | (hd1,args) ->
          let uu____790 =
            let uu____798 =
              let uu____799 = FStar_Syntax_Util.un_uinst hd1 in
              uu____799.FStar_Syntax_Syntax.n in
            (uu____798, args) in
          (match uu____790 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____812)::(assertion,uu____814)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____840 =
                 let uu____842 =
                   unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                     tactic in
                 let uu____844 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____842 uu____844 in
               (match uu____840 with
                | FStar_Tactics_Basic.Success (uu____848,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____856 -> (t, []))
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
        let uu____896 =
          let uu____900 =
            let uu____901 = FStar_Syntax_Subst.compress t in
            uu____901.FStar_Syntax_Syntax.n in
          match uu____900 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____913 = traverse f e t1 in
              (match uu____913 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____931 = traverse f e t1 in
              (match uu____931 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____944;
                 FStar_Syntax_Syntax.pos = uu____945;
                 FStar_Syntax_Syntax.vars = uu____946;_},(p,uu____948)::
               (q,uu____950)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____981 =
                let uu____985 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____985 q in
              (match uu____981 with
               | (q',gs) ->
                   let uu____993 =
                     let uu____994 = FStar_Syntax_Util.mk_imp p q' in
                     uu____994.FStar_Syntax_Syntax.n in
                   (uu____993, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1014 = traverse f e hd1 in
              (match uu____1014 with
               | (hd',gs1) ->
                   let uu____1025 =
                     FStar_List.fold_right
                       (fun uu____1040  ->
                          fun uu____1041  ->
                            match (uu____1040, uu____1041) with
                            | ((a,q),(as',gs)) ->
                                let uu____1084 = traverse f e a in
                                (match uu____1084 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1025 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1152 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1152 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1161 = traverse f e' topen in
                   (match uu____1161 with
                    | (topen',gs) ->
                        let uu____1172 =
                          let uu____1173 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1173.FStar_Syntax_Syntax.n in
                        (uu____1172, gs)))
          | x -> (x, []) in
        match uu____896 with
        | (tn',gs) ->
            let t' =
              let uu___113_1189 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___113_1189.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___113_1189.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___113_1189.FStar_Syntax_Syntax.vars)
              } in
            let uu____1194 = f e t' in
            (match uu____1194 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1219 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1219);
      (let uu____1223 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1223
       then
         let uu____1226 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1226
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1239 = traverse by_tactic_interp env goal in
       match uu____1239 with
       | (t',gs) ->
           ((let uu____1251 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1251
             then
               let uu____1254 =
                 let uu____1255 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1255
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1256 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1254 uu____1256
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1275  ->
                    fun g  ->
                      match uu____1275 with
                      | (n1,gs1) ->
                          ((let uu____1296 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1296
                            then
                              let uu____1299 = FStar_Util.string_of_int n1 in
                              let uu____1300 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1299 uu____1300
                            else ());
                           (let gt' =
                              let uu____1303 =
                                let uu____1304 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1304 in
                              FStar_TypeChecker_Util.label uu____1303
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1310 = s1 in
             match uu____1310 with | (uu____1319,gs1) -> (env, t') :: gs1)))