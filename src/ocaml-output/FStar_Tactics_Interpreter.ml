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
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____62 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_71 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_71.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_71.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_71.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___110_71.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____74 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
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
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____165 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___111_174 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___111_174.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___111_174.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___111_174.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___111_174.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____177 = let uu____179 = unembed_b b in t uu____179 in
              FStar_Tactics_Basic.run uu____177 ps1 in
            let uu____180 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
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
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____301 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___112_310 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___112_310.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___112_310.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___112_310.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___112_310.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____313 =
                let uu____315 = unembed_a a in
                let uu____316 = unembed_b b in t uu____315 uu____316 in
              FStar_Tactics_Basic.run uu____313 ps1 in
            let uu____317 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
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
              FStar_Tactics_Embedding.unembed_state ps embedded_state in
            (match uu____369 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___113_378 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___113_378.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___113_378.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___113_378.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___113_378.FStar_Tactics_Basic.transaction)
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
                   FStar_Tactics_Embedding.embed_result ps1 res
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
    let t_unit1 = FStar_TypeChecker_Common.t_unit in
    let mktac0 name f e_a ta =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 ps f e_a ta) in
    let mktac1 name f u_a e_b tb =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 ps f u_a e_b tb) in
    let mktac2 name f u_a u_b e_c tc =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 ps f u_a u_b e_c tc) in
    let binders_of_env_int nm args =
      match args with
      | (e,uu____625)::[] ->
          let uu____630 =
            let uu____631 =
              let uu____633 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____633 in
            FStar_Reflection_Basic.embed_binders uu____631 in
          Some uu____630
      | uu____634 ->
          let uu____638 =
            let uu____639 = FStar_Ident.string_of_lid nm in
            let uu____640 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____639
              uu____640 in
          failwith uu____638 in
    let uu____642 =
      let uu____644 =
        mktac0 "__forall_intros" FStar_Tactics_Basic.intros
          FStar_Reflection_Basic.embed_binders
          FStar_Reflection_Data.fstar_refl_binders in
      let uu____645 =
        let uu____647 =
          mktac0 "__implies_intro" FStar_Tactics_Basic.imp_intro
            FStar_Reflection_Basic.embed_binder
            FStar_Reflection_Data.fstar_refl_binder in
        let uu____648 =
          let uu____650 =
            mktac0 "__trivial" FStar_Tactics_Basic.trivial
              FStar_Reflection_Basic.embed_unit t_unit1 in
          let uu____651 =
            let uu____653 =
              mktac0 "__revert" FStar_Tactics_Basic.revert
                FStar_Reflection_Basic.embed_unit t_unit1 in
            let uu____654 =
              let uu____656 =
                mktac0 "__clear" FStar_Tactics_Basic.clear
                  FStar_Reflection_Basic.embed_unit t_unit1 in
              let uu____657 =
                let uu____659 =
                  mktac0 "__split" FStar_Tactics_Basic.split
                    FStar_Reflection_Basic.embed_unit t_unit1 in
                let uu____660 =
                  let uu____662 =
                    mktac0 "__merge" FStar_Tactics_Basic.merge_sub_goals
                      FStar_Reflection_Basic.embed_unit t_unit1 in
                  let uu____663 =
                    let uu____665 =
                      mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Reflection_Basic.embed_unit t_unit1 in
                    let uu____666 =
                      let uu____668 =
                        mktac0 "__smt" FStar_Tactics_Basic.smt
                          FStar_Reflection_Basic.embed_unit t_unit1 in
                      let uu____669 =
                        let uu____671 =
                          mktac1 "__exact" FStar_Tactics_Basic.exact
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit1 in
                        let uu____672 =
                          let uu____674 =
                            mktac1 "__apply_lemma"
                              FStar_Tactics_Basic.apply_lemma
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit1 in
                          let uu____675 =
                            let uu____677 =
                              mktac1 "__focus"
                                FStar_Tactics_Basic.focus_cur_goal
                                (unembed_tactic_0
                                   FStar_Reflection_Basic.unembed_unit)
                                FStar_Reflection_Basic.embed_unit t_unit1 in
                            let uu____679 =
                              let uu____681 =
                                mktac2 "__seq" FStar_Tactics_Basic.seq
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  FStar_Reflection_Basic.embed_unit t_unit1 in
                              let uu____684 =
                                let uu____686 =
                                  mktac1 "__prune" FStar_Tactics_Basic.prune
                                    FStar_Reflection_Basic.unembed_string
                                    FStar_Reflection_Basic.embed_unit t_unit1 in
                                let uu____687 =
                                  let uu____689 =
                                    mktac1 "__addns"
                                      FStar_Tactics_Basic.addns
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit1 in
                                  let uu____690 =
                                    let uu____692 =
                                      mktac1 "__print"
                                        (fun x  ->
                                           FStar_Tactics_Basic.tacprint x;
                                           FStar_Tactics_Basic.ret ())
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit1 in
                                    let uu____695 =
                                      let uu____697 =
                                        mktac1 "__dump"
                                          FStar_Tactics_Basic.print_proof_state
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit1 in
                                      let uu____698 =
                                        let uu____700 =
                                          mk1 "__grewrite"
                                            (Prims.parse_int "3")
                                            (grewrite_interpretation ps) in
                                        let uu____701 =
                                          let uu____703 =
                                            mk_refl
                                              ["Syntax"; "__binders_of_env"]
                                              (Prims.parse_int "1")
                                              binders_of_env_int in
                                          [uu____703] in
                                        uu____700 :: uu____701 in
                                      uu____697 :: uu____698 in
                                    uu____692 :: uu____695 in
                                  uu____689 :: uu____690 in
                                uu____686 :: uu____687 in
                              uu____681 :: uu____684 in
                            uu____677 :: uu____679 in
                          uu____674 :: uu____675 in
                        uu____671 :: uu____672 in
                      uu____668 :: uu____669 in
                    uu____665 :: uu____666 in
                  uu____662 :: uu____663 in
                uu____659 :: uu____660 in
              uu____656 :: uu____657 in
            uu____653 :: uu____654 in
          uu____650 :: uu____651 in
        uu____647 :: uu____648 in
      uu____644 :: uu____645 in
    FStar_List.append uu____642
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____712 =
           let uu____713 =
             let uu____714 =
               let uu____715 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____715 in
             [uu____714] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____713 in
         uu____712 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____724 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____729  ->
              let uu____730 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____730) in
       FStar_Tactics_Basic.bind uu____724
         (fun uu____731  ->
            let result =
              let uu____733 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____733 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____735 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____740  ->
                   let uu____741 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____741) in
            FStar_Tactics_Basic.bind uu____735
              (fun uu____742  ->
                 let uu____743 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____743 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____770  ->
                          let uu____771 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____771
                            (fun uu____773  ->
                               let uu____774 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____774
                                 (fun uu____776  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____796  ->
                          let uu____797 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____797
                            (fun uu____799  ->
                               let uu____800 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____800
                                 (fun uu____802  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____806 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____806 with
            | (hd1,args) ->
                let uu____833 =
                  let uu____841 =
                    let uu____842 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____842.FStar_Syntax_Syntax.n in
                  (uu____841, args) in
                (match uu____833 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____853)::(assertion,uu____855)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____881 =
                       let uu____883 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___114_885 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___114_885.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___114_885.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____883
                         (fun uu____886  ->
                            unembed_tactic_0
                              FStar_Reflection_Basic.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal uu____881
                 | uu____887 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____907 = FStar_Syntax_Util.head_and_args t in
      match uu____907 with
      | (hd1,args) ->
          let uu____936 =
            let uu____944 =
              let uu____945 = FStar_Syntax_Util.un_uinst hd1 in
              uu____945.FStar_Syntax_Syntax.n in
            (uu____944, args) in
          (match uu____936 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____958)::(assertion,uu____960)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____986 =
                 let uu____988 =
                   unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                     tactic in
                 let uu____990 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____988 uu____990 in
               (match uu____986 with
                | FStar_Tactics_Basic.Success (uu____994,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____1002 -> (t, []))
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
        let uu____1042 =
          let uu____1046 =
            let uu____1047 = FStar_Syntax_Subst.compress t in
            uu____1047.FStar_Syntax_Syntax.n in
          match uu____1046 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1059 = traverse f e t1 in
              (match uu____1059 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1077 = traverse f e t1 in
              (match uu____1077 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1090;
                 FStar_Syntax_Syntax.pos = uu____1091;
                 FStar_Syntax_Syntax.vars = uu____1092;_},(p,uu____1094)::
               (q,uu____1096)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1127 =
                let uu____1131 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1131 q in
              (match uu____1127 with
               | (q',gs) ->
                   let uu____1139 =
                     let uu____1140 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1140.FStar_Syntax_Syntax.n in
                   (uu____1139, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1160 = traverse f e hd1 in
              (match uu____1160 with
               | (hd',gs1) ->
                   let uu____1171 =
                     FStar_List.fold_right
                       (fun uu____1186  ->
                          fun uu____1187  ->
                            match (uu____1186, uu____1187) with
                            | ((a,q),(as',gs)) ->
                                let uu____1230 = traverse f e a in
                                (match uu____1230 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1171 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1298 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1298 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1307 = traverse f e' topen in
                   (match uu____1307 with
                    | (topen',gs) ->
                        let uu____1318 =
                          let uu____1319 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1319.FStar_Syntax_Syntax.n in
                        (uu____1318, gs)))
          | x -> (x, []) in
        match uu____1042 with
        | (tn',gs) ->
            let t' =
              let uu___115_1335 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___115_1335.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___115_1335.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___115_1335.FStar_Syntax_Syntax.vars)
              } in
            let uu____1340 = f e t' in
            (match uu____1340 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1365 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1365);
      (let uu____1369 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1369
       then
         let uu____1372 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1372
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1385 = traverse by_tactic_interp env goal in
       match uu____1385 with
       | (t',gs) ->
           ((let uu____1397 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1397
             then
               let uu____1400 =
                 let uu____1401 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1401
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1402 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1400 uu____1402
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1421  ->
                    fun g  ->
                      match uu____1421 with
                      | (n1,gs1) ->
                          ((let uu____1442 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1442
                            then
                              let uu____1445 = FStar_Util.string_of_int n1 in
                              let uu____1446 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1445 uu____1446
                            else ());
                           (let gt' =
                              let uu____1449 =
                                let uu____1450 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1450 in
                              FStar_TypeChecker_Util.label uu____1449
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1456 = s1 in
             match uu____1456 with | (uu____1465,gs1) -> (env, t') :: gs1)))