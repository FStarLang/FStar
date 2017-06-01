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
        let uu____574 =
          let uu____576 =
            mktac1 "__norm" FStar_Tactics_Basic.norm
              (FStar_Reflection_Basic.unembed_list
                 FStar_Reflection_Basic.unembed_norm_step)
              FStar_Reflection_Basic.embed_unit t_unit1 in
          let uu____578 =
            let uu____580 =
              mktac0 "__revert" FStar_Tactics_Basic.revert
                FStar_Reflection_Basic.embed_unit t_unit1 in
            let uu____581 =
              let uu____583 =
                mktac0 "__clear" FStar_Tactics_Basic.clear
                  FStar_Reflection_Basic.embed_unit t_unit1 in
              let uu____584 =
                let uu____586 =
                  mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                    FStar_Reflection_Basic.unembed_binder
                    FStar_Reflection_Basic.embed_unit t_unit1 in
                let uu____587 =
                  let uu____589 =
                    mktac0 "__smt" FStar_Tactics_Basic.smt
                      FStar_Reflection_Basic.embed_unit t_unit1 in
                  let uu____590 =
                    let uu____592 =
                      mktac1 "__exact" FStar_Tactics_Basic.exact
                        FStar_Reflection_Basic.unembed_term
                        FStar_Reflection_Basic.embed_unit t_unit1 in
                    let uu____593 =
                      let uu____595 =
                        mktac1 "__apply" FStar_Tactics_Basic.apply
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit1 in
                      let uu____596 =
                        let uu____598 =
                          mktac1 "__apply_lemma"
                            FStar_Tactics_Basic.apply_lemma
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit1 in
                        let uu____599 =
                          let uu____601 =
                            mktac1 "__focus"
                              FStar_Tactics_Basic.focus_cur_goal
                              (unembed_tactic_0
                                 FStar_Reflection_Basic.unembed_unit)
                              FStar_Reflection_Basic.embed_unit t_unit1 in
                          let uu____603 =
                            let uu____605 =
                              mktac2 "__seq" FStar_Tactics_Basic.seq
                                (unembed_tactic_0
                                   FStar_Reflection_Basic.unembed_unit)
                                (unembed_tactic_0
                                   FStar_Reflection_Basic.unembed_unit)
                                FStar_Reflection_Basic.embed_unit t_unit1 in
                            let uu____608 =
                              let uu____610 =
                                mktac1 "__prune" FStar_Tactics_Basic.prune
                                  FStar_Reflection_Basic.unembed_string
                                  FStar_Reflection_Basic.embed_unit t_unit1 in
                              let uu____611 =
                                let uu____613 =
                                  mktac1 "__addns" FStar_Tactics_Basic.addns
                                    FStar_Reflection_Basic.unembed_string
                                    FStar_Reflection_Basic.embed_unit t_unit1 in
                                let uu____614 =
                                  let uu____616 =
                                    mktac1 "__print"
                                      (fun x  ->
                                         FStar_Tactics_Basic.tacprint x;
                                         FStar_Tactics_Basic.ret ())
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit1 in
                                  let uu____619 =
                                    let uu____621 =
                                      mktac1 "__dump"
                                        FStar_Tactics_Basic.print_proof_state
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit1 in
                                    let uu____622 =
                                      let uu____624 =
                                        mktac1 "__dump1"
                                          FStar_Tactics_Basic.print_proof_state1
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit1 in
                                      let uu____625 =
                                        let uu____627 =
                                          mktac1 "__pointwise"
                                            FStar_Tactics_Basic.pointwise
                                            (unembed_tactic_0
                                               FStar_Reflection_Basic.unembed_unit)
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit1 in
                                        let uu____629 =
                                          let uu____631 =
                                            mktac0 "__trefl"
                                              FStar_Tactics_Basic.trefl
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit1 in
                                          let uu____632 =
                                            let uu____634 =
                                              mktac0 "__later"
                                                FStar_Tactics_Basic.later
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit1 in
                                            let uu____635 =
                                              let uu____637 =
                                                mktac0 "__flip"
                                                  FStar_Tactics_Basic.flip
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit1 in
                                              let uu____638 =
                                                let uu____640 =
                                                  mktac0 "__qed"
                                                    FStar_Tactics_Basic.qed
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit1 in
                                                let uu____641 =
                                                  let uu____643 =
                                                    let uu____644 =
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
                                                      uu____644 in
                                                  let uu____647 =
                                                    let uu____649 =
                                                      mk_refl
                                                        ["Syntax";
                                                        "__binders_of_env"]
                                                        (Prims.parse_int "1")
                                                        binders_of_env_int in
                                                    [uu____649] in
                                                  uu____643 :: uu____647 in
                                                uu____640 :: uu____641 in
                                              uu____637 :: uu____638 in
                                            uu____634 :: uu____635 in
                                          uu____631 :: uu____632 in
                                        uu____627 :: uu____629 in
                                      uu____624 :: uu____625 in
                                    uu____621 :: uu____622 in
                                  uu____616 :: uu____619 in
                                uu____613 :: uu____614 in
                              uu____610 :: uu____611 in
                            uu____605 :: uu____608 in
                          uu____601 :: uu____603 in
                        uu____598 :: uu____599 in
                      uu____595 :: uu____596 in
                    uu____592 :: uu____593 in
                  uu____589 :: uu____590 in
                uu____586 :: uu____587 in
              uu____583 :: uu____584 in
            uu____580 :: uu____581 in
          uu____576 :: uu____578 in
        uu____571 :: uu____574 in
      uu____568 :: uu____569 in
    FStar_List.append uu____566
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____658 =
           let uu____659 =
             let uu____660 =
               let uu____661 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals),
                     (proof_state.FStar_Tactics_Basic.smt_goals)) in
               FStar_Syntax_Syntax.as_arg uu____661 in
             [uu____660] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____659 in
         uu____658 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____670 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____675  ->
              let uu____676 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____676) in
       FStar_Tactics_Basic.bind uu____670
         (fun uu____677  ->
            let result =
              let uu____679 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____679 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____681 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____686  ->
                   let uu____687 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____687) in
            FStar_Tactics_Basic.bind uu____681
              (fun uu____688  ->
                 let uu____689 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____689 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____716  ->
                          let uu____717 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____717
                            (fun uu____719  ->
                               let uu____720 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____720
                                 (fun uu____722  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____742  ->
                          let uu____743 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____743
                            (fun uu____745  ->
                               let uu____746 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____746
                                 (fun uu____748  ->
                                    FStar_Tactics_Basic.fail msg))))))
let idterm: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  -> t
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____764 = FStar_Syntax_Util.head_and_args t in
      match uu____764 with
      | (hd1,args) ->
          let uu____793 =
            let uu____801 =
              let uu____802 = FStar_Syntax_Util.un_uinst hd1 in
              uu____802.FStar_Syntax_Syntax.n in
            (uu____801, args) in
          (match uu____793 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(rett,uu____815)::(tactic,uu____817)::(assertion,uu____819)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               (try
                  let ps =
                    FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                  let w =
                    let uu____862 =
                      FStar_List.hd ps.FStar_Tactics_Basic.goals in
                    uu____862.FStar_Tactics_Basic.witness in
                  let uu____863 =
                    let uu____865 =
                      unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                        tactic in
                    FStar_Tactics_Basic.run uu____865 ps in
                  match uu____863 with
                  | FStar_Tactics_Basic.Success (uu____870,ps1) ->
                      ((let uu____873 = FStar_ST.read tacdbg in
                        if uu____873
                        then
                          let uu____876 = FStar_Syntax_Print.term_to_string w in
                          FStar_Util.print1 "Tactic generated proofterm %s\n"
                            uu____876
                        else ());
                       (FStar_Syntax_Util.t_true,
                         (FStar_List.append ps1.FStar_Tactics_Basic.goals
                            ps1.FStar_Tactics_Basic.smt_goals)))
                  | FStar_Tactics_Basic.Failed (s,ps1) ->
                      raise
                        (FStar_Errors.Error
                           ((Prims.strcat "user tactic failed: \""
                               (Prims.strcat s "\"")),
                             (tactic.FStar_Syntax_Syntax.pos)))
                with
                | FStar_Tactics_Basic.Failure s ->
                    raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos)))
                | e1 ->
                    raise
                      (FStar_Errors.Error
                         ("user tactic failed: unexpected exception",
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____896 -> (t, []))
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
        let uu____936 =
          let uu____940 =
            let uu____941 = FStar_Syntax_Subst.compress t in
            uu____941.FStar_Syntax_Syntax.n in
          match uu____940 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____953 = traverse f e t1 in
              (match uu____953 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____971 = traverse f e t1 in
              (match uu____971 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____984;
                 FStar_Syntax_Syntax.pos = uu____985;
                 FStar_Syntax_Syntax.vars = uu____986;_},(p,uu____988)::
               (q,uu____990)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1021 =
                let uu____1025 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1025 q in
              (match uu____1021 with
               | (q',gs) ->
                   let uu____1033 =
                     let uu____1034 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1034.FStar_Syntax_Syntax.n in
                   (uu____1033, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1054 = traverse f e hd1 in
              (match uu____1054 with
               | (hd',gs1) ->
                   let uu____1065 =
                     FStar_List.fold_right
                       (fun uu____1080  ->
                          fun uu____1081  ->
                            match (uu____1080, uu____1081) with
                            | ((a,q),(as',gs)) ->
                                let uu____1124 = traverse f e a in
                                (match uu____1124 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1065 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1192 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1192 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1201 = traverse f e' topen in
                   (match uu____1201 with
                    | (topen',gs) ->
                        let uu____1212 =
                          let uu____1213 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1213.FStar_Syntax_Syntax.n in
                        (uu____1212, gs)))
          | x -> (x, []) in
        match uu____936 with
        | (tn',gs) ->
            let t' =
              let uu___111_1229 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___111_1229.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___111_1229.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___111_1229.FStar_Syntax_Syntax.vars)
              } in
            let uu____1234 = f e t' in
            (match uu____1234 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1259 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1259);
      (let uu____1263 = FStar_ST.read tacdbg in
       if uu____1263
       then
         let uu____1266 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1266
       else ());
      (let uu____1268 = FStar_TypeChecker_Env.clear_expected_typ env in
       match uu____1268 with
       | (env1,uu____1276) ->
           let env2 =
             let uu___112_1280 = env1 in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___112_1280.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___112_1280.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___112_1280.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___112_1280.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___112_1280.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___112_1280.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___112_1280.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___112_1280.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___112_1280.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp = false;
               FStar_TypeChecker_Env.effects =
                 (uu___112_1280.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___112_1280.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___112_1280.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___112_1280.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___112_1280.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___112_1280.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___112_1280.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___112_1280.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___112_1280.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___112_1280.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.type_of =
                 (uu___112_1280.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___112_1280.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___112_1280.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___112_1280.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___112_1280.FStar_TypeChecker_Env.proof_ns)
             } in
           let initial = ((Prims.parse_int "1"), []) in
           let uu____1292 = traverse by_tactic_interp env2 goal in
           (match uu____1292 with
            | (t',gs) ->
                ((let uu____1304 = FStar_ST.read tacdbg in
                  if uu____1304
                  then
                    let uu____1307 =
                      let uu____1308 = FStar_TypeChecker_Env.all_binders env2 in
                      FStar_All.pipe_right uu____1308
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu____1309 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                      uu____1307 uu____1309
                  else ());
                 (let s = initial in
                  let s1 =
                    FStar_List.fold_left
                      (fun uu____1328  ->
                         fun g  ->
                           match uu____1328 with
                           | (n1,gs1) ->
                               let typ =
                                 FStar_TypeChecker_Normalize.normalize []
                                   g.FStar_Tactics_Basic.context
                                   g.FStar_Tactics_Basic.goal_ty in
                               let phi =
                                 let uu____1352 =
                                   FStar_Syntax_Util.un_squash typ in
                                 match uu____1352 with
                                 | Some t -> t
                                 | None  ->
                                     let uu____1365 =
                                       let uu____1366 =
                                         FStar_Syntax_Print.term_to_string
                                           typ in
                                       FStar_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu____1366 in
                                     failwith uu____1365 in
                               ((let uu____1370 = FStar_ST.read tacdbg in
                                 if uu____1370
                                 then
                                   let uu____1373 =
                                     FStar_Util.string_of_int n1 in
                                   let uu____1374 =
                                     FStar_Tactics_Basic.goal_to_string g in
                                   FStar_Util.print2 "Got goal #%s: %s\n"
                                     uu____1373 uu____1374
                                 else ());
                                (let gt' =
                                   let uu____1377 =
                                     let uu____1378 =
                                       FStar_Util.string_of_int n1 in
                                     Prims.strcat "Could not prove goal #"
                                       uu____1378 in
                                   FStar_TypeChecker_Util.label uu____1377
                                     FStar_Range.dummyRange phi in
                                 ((n1 + (Prims.parse_int "1")),
                                   (((g.FStar_Tactics_Basic.context), gt') ::
                                   gs1))))) s gs in
                  let uu____1384 = s1 in
                  match uu____1384 with
                  | (uu____1393,gs1) -> (env2, t') :: gs1))))