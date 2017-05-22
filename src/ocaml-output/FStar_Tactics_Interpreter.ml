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
              let uu___114_71 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___114_71.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___114_71.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___114_71.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___114_71.FStar_Tactics_Basic.transaction)
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
              let uu___115_174 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___115_174.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___115_174.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___115_174.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___115_174.FStar_Tactics_Basic.transaction)
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
              let uu___116_310 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___116_310.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___116_310.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___116_310.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___116_310.FStar_Tactics_Basic.transaction)
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
                   let uu___117_378 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___117_378.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___117_378.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___117_378.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___117_378.FStar_Tactics_Basic.transaction)
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
              mktac0 "__simpl" FStar_Tactics_Basic.simpl
                FStar_Reflection_Basic.embed_unit t_unit1 in
            let uu____654 =
              let uu____656 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit1 in
              let uu____657 =
                let uu____659 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit1 in
                let uu____660 =
                  let uu____662 =
                    mktac0 "__split" FStar_Tactics_Basic.split
                      FStar_Reflection_Basic.embed_unit t_unit1 in
                  let uu____663 =
                    let uu____665 =
                      mktac0 "__merge" FStar_Tactics_Basic.merge_sub_goals
                        FStar_Reflection_Basic.embed_unit t_unit1 in
                    let uu____666 =
                      let uu____668 =
                        mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                          FStar_Reflection_Basic.unembed_binder
                          FStar_Reflection_Basic.embed_unit t_unit1 in
                      let uu____669 =
                        let uu____671 =
                          mktac0 "__smt" FStar_Tactics_Basic.smt
                            FStar_Reflection_Basic.embed_unit t_unit1 in
                        let uu____672 =
                          let uu____674 =
                            mktac1 "__exact" FStar_Tactics_Basic.exact
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit1 in
                          let uu____675 =
                            let uu____677 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit1 in
                            let uu____678 =
                              let uu____680 =
                                mktac1 "__focus"
                                  FStar_Tactics_Basic.focus_cur_goal
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  FStar_Reflection_Basic.embed_unit t_unit1 in
                              let uu____682 =
                                let uu____684 =
                                  mktac2 "__seq" FStar_Tactics_Basic.seq
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    FStar_Reflection_Basic.embed_unit t_unit1 in
                                let uu____687 =
                                  let uu____689 =
                                    mktac1 "__prune"
                                      FStar_Tactics_Basic.prune
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit1 in
                                  let uu____690 =
                                    let uu____692 =
                                      mktac1 "__addns"
                                        FStar_Tactics_Basic.addns
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit1 in
                                    let uu____693 =
                                      let uu____695 =
                                        mktac1 "__print"
                                          (fun x  ->
                                             FStar_Tactics_Basic.tacprint x;
                                             FStar_Tactics_Basic.ret ())
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit1 in
                                      let uu____698 =
                                        let uu____700 =
                                          mktac1 "__dump"
                                            FStar_Tactics_Basic.print_proof_state
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit1 in
                                        let uu____701 =
                                          let uu____703 =
                                            mk1 "__grewrite"
                                              (Prims.parse_int "3")
                                              (grewrite_interpretation ps) in
                                          let uu____704 =
                                            let uu____706 =
                                              mktac1 "__pointwise"
                                                FStar_Tactics_Basic.pointwise
                                                (unembed_tactic_0
                                                   FStar_Reflection_Basic.unembed_unit)
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit1 in
                                            let uu____708 =
                                              let uu____710 =
                                                mktac0 "__refl"
                                                  FStar_Tactics_Basic.refl
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit1 in
                                              let uu____711 =
                                                let uu____713 =
                                                  mk_refl
                                                    ["Syntax";
                                                    "__binders_of_env"]
                                                    (Prims.parse_int "1")
                                                    binders_of_env_int in
                                                [uu____713] in
                                              uu____710 :: uu____711 in
                                            uu____706 :: uu____708 in
                                          uu____703 :: uu____704 in
                                        uu____700 :: uu____701 in
                                      uu____695 :: uu____698 in
                                    uu____692 :: uu____693 in
                                  uu____689 :: uu____690 in
                                uu____684 :: uu____687 in
                              uu____680 :: uu____682 in
                            uu____677 :: uu____678 in
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
         let uu____722 =
           let uu____723 =
             let uu____724 =
               let uu____725 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____725 in
             [uu____724] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____723 in
         uu____722 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____734 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____739  ->
              let uu____740 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____740) in
       FStar_Tactics_Basic.bind uu____734
         (fun uu____741  ->
            let result =
              let uu____743 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____743 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____745 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____750  ->
                   let uu____751 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____751) in
            FStar_Tactics_Basic.bind uu____745
              (fun uu____752  ->
                 let uu____753 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____753 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____780  ->
                          let uu____781 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____781
                            (fun uu____783  ->
                               let uu____784 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____784
                                 (fun uu____786  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____806  ->
                          let uu____807 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____807
                            (fun uu____809  ->
                               let uu____810 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____810
                                 (fun uu____812  ->
                                    FStar_Tactics_Basic.fail msg))))))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____825 = FStar_Syntax_Util.head_and_args t in
      match uu____825 with
      | (hd1,args) ->
          let uu____854 =
            let uu____862 =
              let uu____863 = FStar_Syntax_Util.un_uinst hd1 in
              uu____863.FStar_Syntax_Syntax.n in
            (uu____862, args) in
          (match uu____854 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(rett,uu____876)::(tactic,uu____878)::(assertion,uu____880)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____914 =
                 let uu____916 =
                   unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                     tactic in
                 let uu____918 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____916 uu____918 in
               (match uu____914 with
                | FStar_Tactics_Basic.Success (uu____922,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____930 -> (t, []))
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
        let uu____970 =
          let uu____974 =
            let uu____975 = FStar_Syntax_Subst.compress t in
            uu____975.FStar_Syntax_Syntax.n in
          match uu____974 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____987 = traverse f e t1 in
              (match uu____987 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1005 = traverse f e t1 in
              (match uu____1005 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1018;
                 FStar_Syntax_Syntax.pos = uu____1019;
                 FStar_Syntax_Syntax.vars = uu____1020;_},(p,uu____1022)::
               (q,uu____1024)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1055 =
                let uu____1059 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1059 q in
              (match uu____1055 with
               | (q',gs) ->
                   let uu____1067 =
                     let uu____1068 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1068.FStar_Syntax_Syntax.n in
                   (uu____1067, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1088 = traverse f e hd1 in
              (match uu____1088 with
               | (hd',gs1) ->
                   let uu____1099 =
                     FStar_List.fold_right
                       (fun uu____1114  ->
                          fun uu____1115  ->
                            match (uu____1114, uu____1115) with
                            | ((a,q),(as',gs)) ->
                                let uu____1158 = traverse f e a in
                                (match uu____1158 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1099 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1226 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1226 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1235 = traverse f e' topen in
                   (match uu____1235 with
                    | (topen',gs) ->
                        let uu____1246 =
                          let uu____1247 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1247.FStar_Syntax_Syntax.n in
                        (uu____1246, gs)))
          | x -> (x, []) in
        match uu____970 with
        | (tn',gs) ->
            let t' =
              let uu___118_1263 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___118_1263.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___118_1263.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___118_1263.FStar_Syntax_Syntax.vars)
              } in
            let uu____1268 = f e t' in
            (match uu____1268 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1293 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1293);
      (let uu____1297 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1297
       then
         let uu____1300 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1300
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1313 = traverse by_tactic_interp env goal in
       match uu____1313 with
       | (t',gs) ->
           ((let uu____1325 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1325
             then
               let uu____1328 =
                 let uu____1329 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1329
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1330 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1328 uu____1330
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1349  ->
                    fun g  ->
                      match uu____1349 with
                      | (n1,gs1) ->
                          ((let uu____1370 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1370
                            then
                              let uu____1373 = FStar_Util.string_of_int n1 in
                              let uu____1374 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1373 uu____1374
                            else ());
                           (let gt' =
                              let uu____1377 =
                                let uu____1378 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____1378 in
                              FStar_TypeChecker_Util.label uu____1377
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1384 = s1 in
             match uu____1384 with | (uu____1393,gs1) -> (env, t') :: gs1)))