open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____45)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____59  ->
            let uu____60 = FStar_Ident.string_of_lid nm in
            let uu____61 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____60 uu____61);
       (let uu____62 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____62 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___106_71 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___106_71.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___106_71.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___106_71.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____74 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____74))
  | uu____75 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____135)::(embedded_state,uu____137)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____159  ->
            let uu____160 = FStar_Ident.string_of_lid nm in
            let uu____161 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____160
              uu____161);
       (let uu____162 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____162 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___107_171 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___107_171.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___107_171.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___107_171.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____174 = let uu____176 = unembed_b b in t uu____176 in
              FStar_Tactics_Basic.run uu____174 ps1 in
            let uu____177 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____177))
  | uu____178 ->
      let uu____179 =
        let uu____180 = FStar_Ident.string_of_lid nm in
        let uu____181 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____180 uu____181 in
      failwith uu____179
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____258)::(b,uu____260)::(embedded_state,uu____262)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____292  ->
            let uu____293 = FStar_Ident.string_of_lid nm in
            let uu____294 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____293
              uu____294);
       (let uu____295 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____295 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_304 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_304.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_304.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_304.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____307 =
                let uu____309 = unembed_a a in
                let uu____310 = unembed_b b in t uu____309 uu____310 in
              FStar_Tactics_Basic.run uu____307 ps1 in
            let uu____311 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
            Some uu____311))
  | uu____312 ->
      let uu____313 =
        let uu____314 = FStar_Ident.string_of_lid nm in
        let uu____315 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____314 uu____315 in
      failwith uu____313
let rec primitive_steps:
  FStar_Tactics_Basic.proofstate ->
    FStar_TypeChecker_Normalize.primitive_step Prims.list
  =
  fun ps  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
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
      | (e,uu____549)::[] ->
          let uu____554 =
            let uu____555 =
              let uu____557 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____557 in
            FStar_Reflection_Basic.embed_binders uu____555 in
          Some uu____554
      | uu____558 ->
          let uu____562 =
            let uu____563 = FStar_Ident.string_of_lid nm in
            let uu____564 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____563
              uu____564 in
          failwith uu____562 in
    let uu____566 =
      let uu____568 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit1 in
      let uu____569 =
        let uu____571 =
          mktac0 "__intro" FStar_Tactics_Basic.intro
            FStar_Reflection_Basic.embed_binder
            FStar_Reflection_Data.fstar_refl_binder in
        let uu____572 =
          let uu____574 =
            mktac0 "__intro_irrel" FStar_Tactics_Basic.intro_irrel
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____575 =
            let uu____577 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit1 in
            let uu____579 =
              let uu____581 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit1 in
              let uu____582 =
                let uu____584 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit1 in
                let uu____585 =
                  let uu____587 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit1 in
                  let uu____588 =
                    let uu____590 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit1 in
                    let uu____591 =
                      let uu____593 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit1 in
                      let uu____594 =
                        let uu____596 =
                          mktac1 "__apply" FStar_Tactics_Basic.apply
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit1 in
                        let uu____597 =
                          let uu____599 =
                            mktac1 "__apply_lemma"
                              FStar_Tactics_Basic.apply_lemma
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit1 in
                          let uu____600 =
                            let uu____602 =
                              mktac1 "__focus"
                                FStar_Tactics_Basic.focus_cur_goal
                                (unembed_tactic_0
                                   FStar_Reflection_Basic.unembed_unit)
                                FStar_Reflection_Basic.embed_unit t_unit1 in
                            let uu____604 =
                              let uu____606 =
                                mktac2 "__seq" FStar_Tactics_Basic.seq
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  FStar_Reflection_Basic.embed_unit t_unit1 in
                              let uu____609 =
                                let uu____611 =
                                  mktac1 "__prune" FStar_Tactics_Basic.prune
                                    FStar_Reflection_Basic.unembed_string
                                    FStar_Reflection_Basic.embed_unit t_unit1 in
                                let uu____612 =
                                  let uu____614 =
                                    mktac1 "__addns"
                                      FStar_Tactics_Basic.addns
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit1 in
                                  let uu____615 =
                                    let uu____617 =
                                      mktac1 "__print"
                                        (fun x  ->
                                           FStar_Tactics_Basic.tacprint x;
                                           FStar_Tactics_Basic.ret ())
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit1 in
                                    let uu____620 =
                                      let uu____622 =
                                        mktac1 "__dump"
                                          FStar_Tactics_Basic.print_proof_state
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit1 in
                                      let uu____623 =
                                        let uu____625 =
                                          mktac1 "__pointwise"
                                            FStar_Tactics_Basic.pointwise
                                            (unembed_tactic_0
                                               FStar_Reflection_Basic.unembed_unit)
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit1 in
                                        let uu____627 =
                                          let uu____629 =
                                            mktac0 "__trefl"
                                              FStar_Tactics_Basic.trefl
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit1 in
                                          let uu____630 =
                                            let uu____632 =
                                              mktac0 "__later"
                                                FStar_Tactics_Basic.later
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit1 in
                                            let uu____633 =
                                              let uu____635 =
                                                mktac0 "__flip"
                                                  FStar_Tactics_Basic.flip
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit1 in
                                              let uu____636 =
                                                let uu____638 =
                                                  mktac0 "__qed"
                                                    FStar_Tactics_Basic.qed
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit1 in
                                                let uu____639 =
                                                  let uu____641 =
                                                    let uu____642 =
                                                      FStar_Tactics_Embedding.pair_typ
                                                        FStar_Reflection_Data.fstar_refl_term
                                                        FStar_Reflection_Data.fstar_refl_term in
                                                    mktac1 "__cases"
                                                      FStar_Tactics_Basic.cases
                                                      FStar_Reflection_Basic.unembed_term
                                                      (FStar_Reflection_Basic.embed_pair
                                                         FStar_Reflection_Basic.embed_term
                                                         FStar_Reflection_Data.fstar_refl_term
                                                         FStar_Reflection_Basic.embed_term
                                                         FStar_Reflection_Data.fstar_refl_term)
                                                      uu____642 in
                                                  let uu____645 =
                                                    let uu____647 =
                                                      mk_refl
                                                        ["Syntax";
                                                        "__binders_of_env"]
                                                        (Prims.parse_int "1")
                                                        binders_of_env_int in
                                                    [uu____647] in
                                                  uu____641 :: uu____645 in
                                                uu____638 :: uu____639 in
                                              uu____635 :: uu____636 in
                                            uu____632 :: uu____633 in
                                          uu____629 :: uu____630 in
                                        uu____625 :: uu____627 in
                                      uu____622 :: uu____623 in
                                    uu____617 :: uu____620 in
                                  uu____614 :: uu____615 in
                                uu____611 :: uu____612 in
                              uu____606 :: uu____609 in
                            uu____602 :: uu____604 in
                          uu____599 :: uu____600 in
                        uu____596 :: uu____597 in
                      uu____593 :: uu____594 in
                    uu____590 :: uu____591 in
                  uu____587 :: uu____588 in
                uu____584 :: uu____585 in
              uu____581 :: uu____582 in
            uu____577 :: uu____579 in
          uu____574 :: uu____575 in
        uu____571 :: uu____572 in
      uu____568 :: uu____569 in
    FStar_List.append uu____566
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____656 =
           let uu____657 =
             let uu____658 =
               let uu____659 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals),
                     (proof_state.FStar_Tactics_Basic.smt_goals)) in
               FStar_Syntax_Syntax.as_arg uu____659 in
             [uu____658] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____657 in
         uu____656 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____668 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____673  ->
              let uu____674 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____674) in
       FStar_Tactics_Basic.bind uu____668
         (fun uu____675  ->
            let result =
              let uu____677 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____677 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____679 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____684  ->
                   let uu____685 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____685) in
            FStar_Tactics_Basic.bind uu____679
              (fun uu____686  ->
                 let uu____687 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____687 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____714  ->
                          let uu____715 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____715
                            (fun uu____717  ->
                               let uu____718 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____718
                                 (fun uu____720  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____740  ->
                          let uu____741 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____741
                            (fun uu____743  ->
                               let uu____744 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____744
                                 (fun uu____746  ->
                                    FStar_Tactics_Basic.fail msg))))))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____759 = FStar_Syntax_Util.head_and_args t in
      match uu____759 with
      | (hd1,args) ->
          let uu____788 =
            let uu____796 =
              let uu____797 = FStar_Syntax_Util.un_uinst hd1 in
              uu____797.FStar_Syntax_Syntax.n in
            (uu____796, args) in
          (match uu____788 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(rett,uu____810)::(tactic,uu____812)::(assertion,uu____814)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____848 =
                 let uu____850 =
                   unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                     tactic in
                 let uu____852 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____850 uu____852 in
               (match uu____848 with
                | FStar_Tactics_Basic.Success (uu____856,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____864 -> (t, []))
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
        let uu____904 =
          let uu____908 =
            let uu____909 = FStar_Syntax_Subst.compress t in
            uu____909.FStar_Syntax_Syntax.n in
          match uu____908 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____921 = traverse f e t1 in
              (match uu____921 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____939 = traverse f e t1 in
              (match uu____939 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____952;
                 FStar_Syntax_Syntax.pos = uu____953;
                 FStar_Syntax_Syntax.vars = uu____954;_},(p,uu____956)::
               (q,uu____958)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____989 =
                let uu____993 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____993 q in
              (match uu____989 with
               | (q',gs) ->
                   let uu____1001 =
                     let uu____1002 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1002.FStar_Syntax_Syntax.n in
                   (uu____1001, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1022 = traverse f e hd1 in
              (match uu____1022 with
               | (hd',gs1) ->
                   let uu____1033 =
                     FStar_List.fold_right
                       (fun uu____1048  ->
                          fun uu____1049  ->
                            match (uu____1048, uu____1049) with
                            | ((a,q),(as',gs)) ->
                                let uu____1092 = traverse f e a in
                                (match uu____1092 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1033 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1160 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1160 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1169 = traverse f e' topen in
                   (match uu____1169 with
                    | (topen',gs) ->
                        let uu____1180 =
                          let uu____1181 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1181.FStar_Syntax_Syntax.n in
                        (uu____1180, gs)))
          | x -> (x, []) in
        match uu____904 with
        | (tn',gs) ->
            let t' =
              let uu___109_1197 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___109_1197.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___109_1197.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___109_1197.FStar_Syntax_Syntax.vars)
              } in
            let uu____1202 = f e t' in
            (match uu____1202 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1227 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1227);
      (let uu____1231 = FStar_ST.read tacdbg in
       if uu____1231
       then
         let uu____1234 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1234
       else ());
      (let uu____1236 = FStar_TypeChecker_Env.clear_expected_typ env in
       match uu____1236 with
       | (env1,uu____1244) ->
           let env2 =
             let uu___110_1248 = env1 in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___110_1248.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___110_1248.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___110_1248.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___110_1248.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___110_1248.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___110_1248.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___110_1248.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___110_1248.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___110_1248.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp = false;
               FStar_TypeChecker_Env.effects =
                 (uu___110_1248.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___110_1248.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___110_1248.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___110_1248.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___110_1248.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___110_1248.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___110_1248.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___110_1248.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___110_1248.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___110_1248.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.type_of =
                 (uu___110_1248.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___110_1248.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___110_1248.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___110_1248.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___110_1248.FStar_TypeChecker_Env.proof_ns)
             } in
           let initial = ((Prims.parse_int "1"), []) in
           let uu____1260 = traverse by_tactic_interp env2 goal in
           (match uu____1260 with
            | (t',gs) ->
                ((let uu____1272 = FStar_ST.read tacdbg in
                  if uu____1272
                  then
                    let uu____1275 =
                      let uu____1276 = FStar_TypeChecker_Env.all_binders env2 in
                      FStar_All.pipe_right uu____1276
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu____1277 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                      uu____1275 uu____1277
                  else ());
                 (let s = initial in
                  let s1 =
                    FStar_List.fold_left
                      (fun uu____1296  ->
                         fun g  ->
                           match uu____1296 with
                           | (n1,gs1) ->
                               let typ =
                                 FStar_TypeChecker_Normalize.normalize []
                                   g.FStar_Tactics_Basic.context
                                   g.FStar_Tactics_Basic.goal_ty in
                               let phi =
                                 let uu____1320 =
                                   FStar_Syntax_Util.un_squash typ in
                                 match uu____1320 with
                                 | Some t -> t
                                 | None  ->
                                     let uu____1333 =
                                       let uu____1334 =
                                         FStar_Syntax_Print.term_to_string
                                           typ in
                                       FStar_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu____1334 in
                                     failwith uu____1333 in
                               ((let uu____1338 = FStar_ST.read tacdbg in
                                 if uu____1338
                                 then
                                   let uu____1341 =
                                     FStar_Util.string_of_int n1 in
                                   let uu____1342 =
                                     FStar_Tactics_Basic.goal_to_string g in
                                   FStar_Util.print2 "Got goal #%s: %s\n"
                                     uu____1341 uu____1342
                                 else ());
                                (let gt' =
                                   let uu____1345 =
                                     let uu____1346 =
                                       FStar_Util.string_of_int n1 in
                                     Prims.strcat "Could not prove goal #"
                                       uu____1346 in
                                   FStar_TypeChecker_Util.label uu____1345
                                     FStar_Range.dummyRange phi in
                                 ((n1 + (Prims.parse_int "1")),
                                   (((g.FStar_Tactics_Basic.context), gt') ::
                                   gs1))))) s gs in
                  let uu____1352 = s1 in
                  match uu____1352 with
                  | (uu____1361,gs1) -> (env2, t') :: gs1))))