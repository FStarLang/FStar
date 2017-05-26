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
              let uu___119_71 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___119_71.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___119_71.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___119_71.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___119_71.FStar_Tactics_Basic.transaction)
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
              let uu___120_171 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___120_171.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___120_171.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___120_171.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___120_171.FStar_Tactics_Basic.transaction)
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
              let uu___121_304 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___121_304.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___121_304.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___121_304.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___121_304.FStar_Tactics_Basic.transaction)
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
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____330)::(et2,uu____332)::(embedded_state,uu____334)::[] ->
            let uu____363 =
              FStar_Tactics_Embedding.unembed_state ps embedded_state in
            (match uu____363 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___122_372 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___122_372.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___122_372.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___122_372.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___122_372.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____375 =
                     let uu____377 =
                       FStar_Reflection_Basic.type_of_embedded et1 in
                     let uu____378 =
                       FStar_Reflection_Basic.type_of_embedded et2 in
                     let uu____379 = FStar_Reflection_Basic.unembed_term et1 in
                     let uu____380 = FStar_Reflection_Basic.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____377 uu____378
                       uu____379 uu____380 in
                   FStar_Tactics_Basic.run uu____375 ps1 in
                 let uu____381 =
                   FStar_Tactics_Embedding.embed_result ps1 res
                     FStar_Reflection_Basic.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____381)
        | uu____382 ->
            let uu____383 =
              let uu____384 = FStar_Ident.string_of_lid nm in
              let uu____385 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____384
                uu____385 in
            failwith uu____383
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
      | (e,uu____619)::[] ->
          let uu____624 =
            let uu____625 =
              let uu____627 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____627 in
            FStar_Reflection_Basic.embed_binders uu____625 in
          Some uu____624
      | uu____628 ->
          let uu____632 =
            let uu____633 = FStar_Ident.string_of_lid nm in
            let uu____634 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____633
              uu____634 in
          failwith uu____632 in
    let uu____636 =
      let uu____638 =
        mktac0 "__forall_intros" FStar_Tactics_Basic.intros
          FStar_Reflection_Basic.embed_binders
          FStar_Reflection_Data.fstar_refl_binders in
      let uu____639 =
        let uu____641 =
          mktac0 "__implies_intro" FStar_Tactics_Basic.imp_intro
            FStar_Reflection_Basic.embed_binder
            FStar_Reflection_Data.fstar_refl_binder in
        let uu____642 =
          let uu____644 =
            mktac0 "__trivial" FStar_Tactics_Basic.trivial
              FStar_Reflection_Basic.embed_unit t_unit1 in
          let uu____645 =
            let uu____647 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit1 in
            let uu____649 =
              let uu____651 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit1 in
              let uu____652 =
                let uu____654 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit1 in
                let uu____655 =
                  let uu____657 =
                    mktac0 "__split" FStar_Tactics_Basic.split
                      FStar_Reflection_Basic.embed_unit t_unit1 in
                  let uu____658 =
                    let uu____660 =
                      mktac0 "__merge" FStar_Tactics_Basic.merge_sub_goals
                        FStar_Reflection_Basic.embed_unit t_unit1 in
                    let uu____661 =
                      let uu____663 =
                        mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                          FStar_Reflection_Basic.unembed_binder
                          FStar_Reflection_Basic.embed_unit t_unit1 in
                      let uu____664 =
                        let uu____666 =
                          mktac0 "__smt" FStar_Tactics_Basic.smt
                            FStar_Reflection_Basic.embed_unit t_unit1 in
                        let uu____667 =
                          let uu____669 =
                            mktac1 "__exact" FStar_Tactics_Basic.exact
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit1 in
                          let uu____670 =
                            let uu____672 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit1 in
                            let uu____673 =
                              let uu____675 =
                                mktac1 "__focus"
                                  FStar_Tactics_Basic.focus_cur_goal
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  FStar_Reflection_Basic.embed_unit t_unit1 in
                              let uu____677 =
                                let uu____679 =
                                  mktac2 "__seq" FStar_Tactics_Basic.seq
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    FStar_Reflection_Basic.embed_unit t_unit1 in
                                let uu____682 =
                                  let uu____684 =
                                    mktac1 "__prune"
                                      FStar_Tactics_Basic.prune
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit1 in
                                  let uu____685 =
                                    let uu____687 =
                                      mktac1 "__addns"
                                        FStar_Tactics_Basic.addns
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit1 in
                                    let uu____688 =
                                      let uu____690 =
                                        mktac1 "__print"
                                          (fun x  ->
                                             FStar_Tactics_Basic.tacprint x;
                                             FStar_Tactics_Basic.ret ())
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit1 in
                                      let uu____693 =
                                        let uu____695 =
                                          mktac1 "__dump"
                                            FStar_Tactics_Basic.print_proof_state
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit1 in
                                        let uu____696 =
                                          let uu____698 =
                                            mk1 "__grewrite"
                                              (Prims.parse_int "3")
                                              (grewrite_interpretation ps) in
                                          let uu____699 =
                                            let uu____701 =
                                              mktac1 "__pointwise"
                                                FStar_Tactics_Basic.pointwise
                                                (unembed_tactic_0
                                                   FStar_Reflection_Basic.unembed_unit)
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit1 in
                                            let uu____703 =
                                              let uu____705 =
                                                mktac0 "__trefl"
                                                  FStar_Tactics_Basic.trefl
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit1 in
                                              let uu____706 =
                                                let uu____708 =
                                                  mktac0 "__later"
                                                    FStar_Tactics_Basic.later
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit1 in
                                                let uu____709 =
                                                  let uu____711 =
                                                    mktac0 "__qed"
                                                      FStar_Tactics_Basic.qed
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit1 in
                                                  let uu____712 =
                                                    let uu____714 =
                                                      let uu____715 =
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
                                                        uu____715 in
                                                    let uu____718 =
                                                      let uu____720 =
                                                        mktac1 "__unsquash"
                                                          FStar_Tactics_Basic.unsquash
                                                          FStar_Reflection_Basic.unembed_term
                                                          FStar_Reflection_Basic.embed_term
                                                          FStar_Reflection_Data.fstar_refl_term in
                                                      let uu____721 =
                                                        let uu____723 =
                                                          mk_refl
                                                            ["Syntax";
                                                            "__binders_of_env"]
                                                            (Prims.parse_int
                                                               "1")
                                                            binders_of_env_int in
                                                        [uu____723] in
                                                      uu____720 :: uu____721 in
                                                    uu____714 :: uu____718 in
                                                  uu____711 :: uu____712 in
                                                uu____708 :: uu____709 in
                                              uu____705 :: uu____706 in
                                            uu____701 :: uu____703 in
                                          uu____698 :: uu____699 in
                                        uu____695 :: uu____696 in
                                      uu____690 :: uu____693 in
                                    uu____687 :: uu____688 in
                                  uu____684 :: uu____685 in
                                uu____679 :: uu____682 in
                              uu____675 :: uu____677 in
                            uu____672 :: uu____673 in
                          uu____669 :: uu____670 in
                        uu____666 :: uu____667 in
                      uu____663 :: uu____664 in
                    uu____660 :: uu____661 in
                  uu____657 :: uu____658 in
                uu____654 :: uu____655 in
              uu____651 :: uu____652 in
            uu____647 :: uu____649 in
          uu____644 :: uu____645 in
        uu____641 :: uu____642 in
      uu____638 :: uu____639 in
    FStar_List.append uu____636
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____732 =
           let uu____733 =
             let uu____734 =
               let uu____735 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____735 in
             [uu____734] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____733 in
         uu____732 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____744 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____749  ->
              let uu____750 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____750) in
       FStar_Tactics_Basic.bind uu____744
         (fun uu____751  ->
            let result =
              let uu____753 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____753 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____755 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____760  ->
                   let uu____761 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____761) in
            FStar_Tactics_Basic.bind uu____755
              (fun uu____762  ->
                 let uu____763 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____763 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____790  ->
                          let uu____791 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____791
                            (fun uu____793  ->
                               let uu____794 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____794
                                 (fun uu____796  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____816  ->
                          let uu____817 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____817
                            (fun uu____819  ->
                               let uu____820 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____820
                                 (fun uu____822  ->
                                    FStar_Tactics_Basic.fail msg))))))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____835 = FStar_Syntax_Util.head_and_args t in
      match uu____835 with
      | (hd1,args) ->
          let uu____864 =
            let uu____872 =
              let uu____873 = FStar_Syntax_Util.un_uinst hd1 in
              uu____873.FStar_Syntax_Syntax.n in
            (uu____872, args) in
          (match uu____864 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(rett,uu____886)::(tactic,uu____888)::(assertion,uu____890)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____924 =
                 let uu____926 =
                   unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                     tactic in
                 let uu____928 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____926 uu____928 in
               (match uu____924 with
                | FStar_Tactics_Basic.Success (uu____932,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____940 -> (t, []))
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
        let uu____980 =
          let uu____984 =
            let uu____985 = FStar_Syntax_Subst.compress t in
            uu____985.FStar_Syntax_Syntax.n in
          match uu____984 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____997 = traverse f e t1 in
              (match uu____997 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1015 = traverse f e t1 in
              (match uu____1015 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1028;
                 FStar_Syntax_Syntax.pos = uu____1029;
                 FStar_Syntax_Syntax.vars = uu____1030;_},(p,uu____1032)::
               (q,uu____1034)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1065 =
                let uu____1069 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1069 q in
              (match uu____1065 with
               | (q',gs) ->
                   let uu____1077 =
                     let uu____1078 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1078.FStar_Syntax_Syntax.n in
                   (uu____1077, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1098 = traverse f e hd1 in
              (match uu____1098 with
               | (hd',gs1) ->
                   let uu____1109 =
                     FStar_List.fold_right
                       (fun uu____1124  ->
                          fun uu____1125  ->
                            match (uu____1124, uu____1125) with
                            | ((a,q),(as',gs)) ->
                                let uu____1168 = traverse f e a in
                                (match uu____1168 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1109 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1236 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1236 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1245 = traverse f e' topen in
                   (match uu____1245 with
                    | (topen',gs) ->
                        let uu____1256 =
                          let uu____1257 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1257.FStar_Syntax_Syntax.n in
                        (uu____1256, gs)))
          | x -> (x, []) in
        match uu____980 with
        | (tn',gs) ->
            let t' =
              let uu___123_1273 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___123_1273.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___123_1273.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___123_1273.FStar_Syntax_Syntax.vars)
              } in
            let uu____1278 = f e t' in
            (match uu____1278 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1303 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1303);
      (let uu____1307 = FStar_ST.read tacdbg in
       if uu____1307
       then
         let uu____1310 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1310
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1323 = traverse by_tactic_interp env goal in
       match uu____1323 with
       | (t',gs) ->
           ((let uu____1335 = FStar_ST.read tacdbg in
             if uu____1335
             then
               let uu____1338 =
                 let uu____1339 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1339
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1340 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1338 uu____1340
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1359  ->
                    fun g  ->
                      match uu____1359 with
                      | (n1,gs1) ->
                          ((let uu____1380 = FStar_ST.read tacdbg in
                            if uu____1380
                            then
                              let uu____1383 = FStar_Util.string_of_int n1 in
                              let uu____1384 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1383 uu____1384
                            else ());
                           (let gt' =
                              let uu____1387 =
                                let uu____1388 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____1388 in
                              FStar_TypeChecker_Util.label uu____1387
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1394 = s1 in
             match uu____1394 with | (uu____1403,gs1) -> (env, t') :: gs1)))