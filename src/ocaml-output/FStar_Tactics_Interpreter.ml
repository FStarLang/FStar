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
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit1 in
            let uu____655 =
              let uu____657 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit1 in
              let uu____658 =
                let uu____660 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit1 in
                let uu____661 =
                  let uu____663 =
                    mktac0 "__split" FStar_Tactics_Basic.split
                      FStar_Reflection_Basic.embed_unit t_unit1 in
                  let uu____664 =
                    let uu____666 =
                      mktac0 "__merge" FStar_Tactics_Basic.merge_sub_goals
                        FStar_Reflection_Basic.embed_unit t_unit1 in
                    let uu____667 =
                      let uu____669 =
                        mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                          FStar_Reflection_Basic.unembed_binder
                          FStar_Reflection_Basic.embed_unit t_unit1 in
                      let uu____670 =
                        let uu____672 =
                          mktac0 "__smt" FStar_Tactics_Basic.smt
                            FStar_Reflection_Basic.embed_unit t_unit1 in
                        let uu____673 =
                          let uu____675 =
                            mktac1 "__exact" FStar_Tactics_Basic.exact
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit1 in
                          let uu____676 =
                            let uu____678 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit1 in
                            let uu____679 =
                              let uu____681 =
                                mktac1 "__focus"
                                  FStar_Tactics_Basic.focus_cur_goal
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  FStar_Reflection_Basic.embed_unit t_unit1 in
                              let uu____683 =
                                let uu____685 =
                                  mktac2 "__seq" FStar_Tactics_Basic.seq
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    FStar_Reflection_Basic.embed_unit t_unit1 in
                                let uu____688 =
                                  let uu____690 =
                                    mktac1 "__prune"
                                      FStar_Tactics_Basic.prune
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit1 in
                                  let uu____691 =
                                    let uu____693 =
                                      mktac1 "__addns"
                                        FStar_Tactics_Basic.addns
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit1 in
                                    let uu____694 =
                                      let uu____696 =
                                        mktac1 "__print"
                                          (fun x  ->
                                             FStar_Tactics_Basic.tacprint x;
                                             FStar_Tactics_Basic.ret ())
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit1 in
                                      let uu____699 =
                                        let uu____701 =
                                          mktac1 "__dump"
                                            FStar_Tactics_Basic.print_proof_state
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit1 in
                                        let uu____702 =
                                          let uu____704 =
                                            mk1 "__grewrite"
                                              (Prims.parse_int "3")
                                              (grewrite_interpretation ps) in
                                          let uu____705 =
                                            let uu____707 =
                                              mktac1 "__pointwise"
                                                FStar_Tactics_Basic.pointwise
                                                (unembed_tactic_0
                                                   FStar_Reflection_Basic.unembed_unit)
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit1 in
                                            let uu____709 =
                                              let uu____711 =
                                                mktac0 "__trefl"
                                                  FStar_Tactics_Basic.trefl
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit1 in
                                              let uu____712 =
                                                let uu____714 =
                                                  mktac0 "__later"
                                                    FStar_Tactics_Basic.later
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit1 in
                                                let uu____715 =
                                                  let uu____717 =
                                                    mk_refl
                                                      ["Syntax";
                                                      "__binders_of_env"]
                                                      (Prims.parse_int "1")
                                                      binders_of_env_int in
                                                  [uu____717] in
                                                uu____714 :: uu____715 in
                                              uu____711 :: uu____712 in
                                            uu____707 :: uu____709 in
                                          uu____704 :: uu____705 in
                                        uu____701 :: uu____702 in
                                      uu____696 :: uu____699 in
                                    uu____693 :: uu____694 in
                                  uu____690 :: uu____691 in
                                uu____685 :: uu____688 in
                              uu____681 :: uu____683 in
                            uu____678 :: uu____679 in
                          uu____675 :: uu____676 in
                        uu____672 :: uu____673 in
                      uu____669 :: uu____670 in
                    uu____666 :: uu____667 in
                  uu____663 :: uu____664 in
                uu____660 :: uu____661 in
              uu____657 :: uu____658 in
            uu____653 :: uu____655 in
          uu____650 :: uu____651 in
        uu____647 :: uu____648 in
      uu____644 :: uu____645 in
    FStar_List.append uu____642
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____726 =
           let uu____727 =
             let uu____728 =
               let uu____729 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____729 in
             [uu____728] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____727 in
         uu____726 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____738 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____743  ->
              let uu____744 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____744) in
       FStar_Tactics_Basic.bind uu____738
         (fun uu____745  ->
            let result =
              let uu____747 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____747 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____749 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____754  ->
                   let uu____755 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____755) in
            FStar_Tactics_Basic.bind uu____749
              (fun uu____756  ->
                 let uu____757 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____757 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____784  ->
                          let uu____785 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____785
                            (fun uu____787  ->
                               let uu____788 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____788
                                 (fun uu____790  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____810  ->
                          let uu____811 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____811
                            (fun uu____813  ->
                               let uu____814 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____814
                                 (fun uu____816  ->
                                    FStar_Tactics_Basic.fail msg))))))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____829 = FStar_Syntax_Util.head_and_args t in
      match uu____829 with
      | (hd1,args) ->
          let uu____858 =
            let uu____866 =
              let uu____867 = FStar_Syntax_Util.un_uinst hd1 in
              uu____867.FStar_Syntax_Syntax.n in
            (uu____866, args) in
          (match uu____858 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(rett,uu____880)::(tactic,uu____882)::(assertion,uu____884)::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____918 =
                 let uu____920 =
                   unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                     tactic in
                 let uu____922 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____920 uu____922 in
               (match uu____918 with
                | FStar_Tactics_Basic.Success (uu____926,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____934 -> (t, []))
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
        let uu____974 =
          let uu____978 =
            let uu____979 = FStar_Syntax_Subst.compress t in
            uu____979.FStar_Syntax_Syntax.n in
          match uu____978 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____991 = traverse f e t1 in
              (match uu____991 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1009 = traverse f e t1 in
              (match uu____1009 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1022;
                 FStar_Syntax_Syntax.pos = uu____1023;
                 FStar_Syntax_Syntax.vars = uu____1024;_},(p,uu____1026)::
               (q,uu____1028)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1059 =
                let uu____1063 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1063 q in
              (match uu____1059 with
               | (q',gs) ->
                   let uu____1071 =
                     let uu____1072 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1072.FStar_Syntax_Syntax.n in
                   (uu____1071, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1092 = traverse f e hd1 in
              (match uu____1092 with
               | (hd',gs1) ->
                   let uu____1103 =
                     FStar_List.fold_right
                       (fun uu____1118  ->
                          fun uu____1119  ->
                            match (uu____1118, uu____1119) with
                            | ((a,q),(as',gs)) ->
                                let uu____1162 = traverse f e a in
                                (match uu____1162 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1103 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1230 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1230 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1239 = traverse f e' topen in
                   (match uu____1239 with
                    | (topen',gs) ->
                        let uu____1250 =
                          let uu____1251 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1251.FStar_Syntax_Syntax.n in
                        (uu____1250, gs)))
          | x -> (x, []) in
        match uu____974 with
        | (tn',gs) ->
            let t' =
              let uu___118_1267 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___118_1267.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___118_1267.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___118_1267.FStar_Syntax_Syntax.vars)
              } in
            let uu____1272 = f e t' in
            (match uu____1272 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1297 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1297);
      (let uu____1301 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1301
       then
         let uu____1304 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1304
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1317 = traverse by_tactic_interp env goal in
       match uu____1317 with
       | (t',gs) ->
           ((let uu____1329 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1329
             then
               let uu____1332 =
                 let uu____1333 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1333
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1334 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1332 uu____1334
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1353  ->
                    fun g  ->
                      match uu____1353 with
                      | (n1,gs1) ->
                          ((let uu____1374 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1374
                            then
                              let uu____1377 = FStar_Util.string_of_int n1 in
                              let uu____1378 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1377 uu____1378
                            else ());
                           (let gt' =
                              let uu____1381 =
                                let uu____1382 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____1382 in
                              FStar_TypeChecker_Util.label uu____1381
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1388 = s1 in
             match uu____1388 with | (uu____1397,gs1) -> (env, t') :: gs1)))