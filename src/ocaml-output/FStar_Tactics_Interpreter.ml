open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let t_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_unit
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____47)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____61  ->
            let uu____62 = FStar_Ident.string_of_lid nm in
            let uu____63 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____62 uu____63);
       (let uu____64 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____64 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_73 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_73.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_73.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_73.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____76 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____76))
  | uu____77 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____137)::(embedded_state,uu____139)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____161  ->
            let uu____162 = FStar_Ident.string_of_lid nm in
            let uu____163 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____162
              uu____163);
       (let uu____164 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____164 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_173 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_173.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_173.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_173.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____176 = let uu____178 = unembed_b b in t uu____178 in
              FStar_Tactics_Basic.run uu____176 ps1 in
            let uu____179 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____179))
  | uu____180 ->
      let uu____181 =
        let uu____182 = FStar_Ident.string_of_lid nm in
        let uu____183 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____182 uu____183 in
      failwith uu____181
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____260)::(b,uu____262)::(embedded_state,uu____264)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____294  ->
            let uu____295 = FStar_Ident.string_of_lid nm in
            let uu____296 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____295
              uu____296);
       (let uu____297 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____297 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_306 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_306.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_306.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_306.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____309 =
                let uu____311 = unembed_a a in
                let uu____312 = unembed_b b in t uu____311 uu____312 in
              FStar_Tactics_Basic.run uu____309 ps1 in
            let uu____313 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
            Some uu____313))
  | uu____314 ->
      let uu____315 =
        let uu____316 = FStar_Ident.string_of_lid nm in
        let uu____317 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____316 uu____317 in
      failwith uu____315
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
      | (e,uu____548)::[] ->
          let uu____553 =
            let uu____554 =
              let uu____556 = FStar_Tactics_Embedding.unembed_env ps e in
              FStar_TypeChecker_Env.all_binders uu____556 in
            FStar_Reflection_Basic.embed_binders uu____554 in
          Some uu____553
      | uu____557 ->
          let uu____561 =
            let uu____562 = FStar_Ident.string_of_lid nm in
            let uu____563 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.format2 "Unexpected application %s %s" uu____562
              uu____563 in
          failwith uu____561 in
    let uu____565 =
      let uu____567 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Reflection_Basic.embed_unit t_unit in
      let uu____568 =
        let uu____570 =
          mktac2 "__trytac" (fun uu____573  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit) t_unit in
        let uu____577 =
          let uu____579 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____582 =
            let uu____584 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit in
            let uu____586 =
              let uu____588 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit in
              let uu____589 =
                let uu____591 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit in
                let uu____592 =
                  let uu____594 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit in
                  let uu____595 =
                    let uu____597 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit in
                    let uu____598 =
                      let uu____600 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit in
                      let uu____601 =
                        let uu____603 =
                          mktac1 "__exact_lemma"
                            FStar_Tactics_Basic.exact_lemma
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit in
                        let uu____604 =
                          let uu____606 =
                            mktac1 "__apply" FStar_Tactics_Basic.apply
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit in
                          let uu____607 =
                            let uu____609 =
                              mktac1 "__apply_lemma"
                                FStar_Tactics_Basic.apply_lemma
                                FStar_Reflection_Basic.unembed_term
                                FStar_Reflection_Basic.embed_unit t_unit in
                            let uu____610 =
                              let uu____612 =
                                mktac1 "__focus"
                                  FStar_Tactics_Basic.focus_cur_goal
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  FStar_Reflection_Basic.embed_unit t_unit in
                              let uu____614 =
                                let uu____616 =
                                  mktac2 "__seq" FStar_Tactics_Basic.seq
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    (unembed_tactic_0
                                       FStar_Reflection_Basic.unembed_unit)
                                    FStar_Reflection_Basic.embed_unit t_unit in
                                let uu____619 =
                                  let uu____621 =
                                    mktac1 "__prune"
                                      FStar_Tactics_Basic.prune
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit in
                                  let uu____622 =
                                    let uu____624 =
                                      mktac1 "__addns"
                                        FStar_Tactics_Basic.addns
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit in
                                    let uu____625 =
                                      let uu____627 =
                                        mktac1 "__print"
                                          (fun x  ->
                                             FStar_Tactics_Basic.tacprint x;
                                             FStar_Tactics_Basic.ret ())
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit in
                                      let uu____630 =
                                        let uu____632 =
                                          mktac1 "__dump"
                                            FStar_Tactics_Basic.print_proof_state
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit in
                                        let uu____633 =
                                          let uu____635 =
                                            mktac1 "__dump1"
                                              FStar_Tactics_Basic.print_proof_state1
                                              FStar_Reflection_Basic.unembed_string
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit in
                                          let uu____636 =
                                            let uu____638 =
                                              mktac1 "__pointwise"
                                                FStar_Tactics_Basic.pointwise
                                                (unembed_tactic_0
                                                   FStar_Reflection_Basic.unembed_unit)
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit in
                                            let uu____640 =
                                              let uu____642 =
                                                mktac0 "__trefl"
                                                  FStar_Tactics_Basic.trefl
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit in
                                              let uu____643 =
                                                let uu____645 =
                                                  mktac0 "__later"
                                                    FStar_Tactics_Basic.later
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit in
                                                let uu____646 =
                                                  let uu____648 =
                                                    mktac0 "__flip"
                                                      FStar_Tactics_Basic.flip
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit in
                                                  let uu____649 =
                                                    let uu____651 =
                                                      mktac0 "__qed"
                                                        FStar_Tactics_Basic.qed
                                                        FStar_Reflection_Basic.embed_unit
                                                        t_unit in
                                                    let uu____652 =
                                                      let uu____654 =
                                                        let uu____655 =
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
                                                          uu____655 in
                                                      let uu____658 =
                                                        let uu____660 =
                                                          mk_refl
                                                            ["Syntax";
                                                            "__binders_of_env"]
                                                            (Prims.parse_int
                                                               "1")
                                                            binders_of_env_int in
                                                        [uu____660] in
                                                      uu____654 :: uu____658 in
                                                    uu____651 :: uu____652 in
                                                  uu____648 :: uu____649 in
                                                uu____645 :: uu____646 in
                                              uu____642 :: uu____643 in
                                            uu____638 :: uu____640 in
                                          uu____635 :: uu____636 in
                                        uu____632 :: uu____633 in
                                      uu____627 :: uu____630 in
                                    uu____624 :: uu____625 in
                                  uu____621 :: uu____622 in
                                uu____616 :: uu____619 in
                              uu____612 :: uu____614 in
                            uu____609 :: uu____610 in
                          uu____606 :: uu____607 in
                        uu____603 :: uu____604 in
                      uu____600 :: uu____601 in
                    uu____597 :: uu____598 in
                  uu____594 :: uu____595 in
                uu____591 :: uu____592 in
              uu____588 :: uu____589 in
            uu____584 :: uu____586 in
          uu____579 :: uu____582 in
        uu____570 :: uu____577 in
      uu____567 :: uu____568 in
    FStar_List.append uu____565
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____669 =
           let uu____670 =
             let uu____671 =
               let uu____672 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals),
                     (proof_state.FStar_Tactics_Basic.smt_goals)) in
               FStar_Syntax_Syntax.as_arg uu____672 in
             [uu____671] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____670 in
         uu____669 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____681 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____686  ->
              let uu____687 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____687) in
       FStar_Tactics_Basic.bind uu____681
         (fun uu____688  ->
            let result =
              let uu____690 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____690 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____692 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____697  ->
                   let uu____698 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____698) in
            FStar_Tactics_Basic.bind uu____692
              (fun uu____699  ->
                 let uu____700 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____700 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____727  ->
                          let uu____728 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____728
                            (fun uu____730  ->
                               let uu____731 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____731
                                 (fun uu____733  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____753  ->
                          let uu____754 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____754
                            (fun uu____756  ->
                               let uu____757 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____757
                                 (fun uu____759  ->
                                    FStar_Tactics_Basic.fail msg))))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____763 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____767 -> false
let flip: pol -> pol = fun p  -> match p with | Pos  -> Neg | Neg  -> Pos
let by_tactic_interp:
  pol ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____786 = FStar_Syntax_Util.head_and_args t in
        match uu____786 with
        | (hd1,args) ->
            let uu____815 =
              let uu____823 =
                let uu____824 = FStar_Syntax_Util.un_uinst hd1 in
                uu____824.FStar_Syntax_Syntax.n in
              (uu____823, args) in
            (match uu____815 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____837)::(tactic,uu____839)::(assertion,uu____841)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____880)::(tactic,uu____882)::(assertion,uu____884)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let ps =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 let w =
                   let uu____920 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
                   uu____920.FStar_Tactics_Basic.witness in
                 let r =
                   try
                     let uu____926 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     FStar_Tactics_Basic.run uu____926 ps
                   with
                   | FStar_Tactics_Basic.TacFailure s ->
                       FStar_Tactics_Basic.Failed
                         ((Prims.strcat "EXCEPTION: " s), ps) in
                 (match r with
                  | FStar_Tactics_Basic.Success (uu____934,ps1) ->
                      ((let uu____937 = FStar_ST.read tacdbg in
                        if uu____937
                        then
                          let uu____940 = FStar_Syntax_Print.term_to_string w in
                          FStar_Util.print1 "Tactic generated proofterm %s\n"
                            uu____940
                        else ());
                       (FStar_Syntax_Util.t_true,
                         (FStar_List.append ps1.FStar_Tactics_Basic.goals
                            ps1.FStar_Tactics_Basic.smt_goals)))
                  | FStar_Tactics_Basic.Failed (s,ps1) ->
                      ((let uu____946 =
                          FStar_Util.format1 "user tactic failed: %s" s in
                        FStar_Errors.err assertion.FStar_Syntax_Syntax.pos
                          uu____946);
                       (t, [])))
             | uu____948 -> (t, []))
let rec traverse:
  (pol ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list))
    ->
    pol ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let uu____996 =
            let uu____1000 =
              let uu____1001 = FStar_Syntax_Subst.compress t in
              uu____1001.FStar_Syntax_Syntax.n in
            match uu____1000 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1013 = traverse f pol e t1 in
                (match uu____1013 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1031 = traverse f pol e t1 in
                (match uu____1031 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1044;
                   FStar_Syntax_Syntax.pos = uu____1045;
                   FStar_Syntax_Syntax.vars = uu____1046;_},(p,uu____1048)::
                 (q,uu____1050)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p in
                let uu____1081 =
                  let uu____1085 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1085 p in
                (match uu____1081 with
                 | (p',gs1) ->
                     let uu____1093 =
                       let uu____1097 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1097 q in
                     (match uu____1093 with
                      | (q',gs2) ->
                          let uu____1105 =
                            let uu____1106 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1106.FStar_Syntax_Syntax.n in
                          (uu____1105, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1126 = traverse f pol e hd1 in
                (match uu____1126 with
                 | (hd',gs1) ->
                     let uu____1137 =
                       FStar_List.fold_right
                         (fun uu____1152  ->
                            fun uu____1153  ->
                              match (uu____1152, uu____1153) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1196 = traverse f pol e a in
                                  (match uu____1196 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1137 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1264 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1264 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1273 =
                       let uu____1281 =
                         FStar_List.map
                           (fun uu____1295  ->
                              match uu____1295 with
                              | (bv,aq) ->
                                  let uu____1305 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____1305 with
                                   | (s',gs) ->
                                       (((let uu___113_1321 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___113_1321.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___113_1321.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____1281 in
                     (match uu____1273 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____1355 = traverse f pol e' topen in
                          (match uu____1355 with
                           | (topen',gs2) ->
                               let uu____1366 =
                                 let uu____1367 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____1367.FStar_Syntax_Syntax.n in
                               (uu____1366, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____996 with
          | (tn',gs) ->
              let t' =
                let uu___114_1383 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___114_1383.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___114_1383.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___114_1383.FStar_Syntax_Syntax.vars)
                } in
              let uu____1388 = f pol e t' in
              (match uu____1388 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let getprop:
  FStar_Tactics_Basic.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t in
      let uu____1409 = FStar_Syntax_Util.un_squash tn in
      match uu____1409 with
      | Some t' -> Some t'
      | None  ->
          let uu____1423 = FStar_Syntax_Util.head_and_args tn in
          (match uu____1423 with
           | (hd1,uu____1435) ->
               let uu____1450 =
                 let uu____1451 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____1451.FStar_Syntax_Syntax.n in
               (match uu____1450 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid
                    -> Some t
                | uu____1456 -> None))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1470 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1470);
      (let uu____1474 = FStar_ST.read tacdbg in
       if uu____1474
       then
         let uu____1477 =
           let uu____1478 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____1478
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____1479 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____1477
           uu____1479
       else ());
      (let uu____1481 = FStar_TypeChecker_Env.clear_expected_typ env in
       match uu____1481 with
       | (env1,uu____1489) ->
           let env2 =
             let uu___115_1493 = env1 in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___115_1493.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___115_1493.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___115_1493.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___115_1493.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___115_1493.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___115_1493.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___115_1493.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___115_1493.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___115_1493.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp = false;
               FStar_TypeChecker_Env.effects =
                 (uu___115_1493.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___115_1493.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___115_1493.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___115_1493.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___115_1493.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___115_1493.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___115_1493.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___115_1493.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___115_1493.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___115_1493.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.type_of =
                 (uu___115_1493.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___115_1493.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___115_1493.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___115_1493.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___115_1493.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___115_1493.FStar_TypeChecker_Env.synth)
             } in
           let initial = ((Prims.parse_int "1"), []) in
           let uu____1505 = traverse by_tactic_interp Pos env2 goal in
           (match uu____1505 with
            | (t',gs) ->
                ((let uu____1517 = FStar_ST.read tacdbg in
                  if uu____1517
                  then
                    let uu____1520 =
                      let uu____1521 = FStar_TypeChecker_Env.all_binders env2 in
                      FStar_All.pipe_right uu____1521
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu____1522 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                      uu____1520 uu____1522
                  else ());
                 (let s = initial in
                  let s1 =
                    FStar_List.fold_left
                      (fun uu____1541  ->
                         fun g  ->
                           match uu____1541 with
                           | (n1,gs1) ->
                               let phi =
                                 let uu____1562 =
                                   getprop g.FStar_Tactics_Basic.context
                                     g.FStar_Tactics_Basic.goal_ty in
                                 match uu____1562 with
                                 | None  ->
                                     let uu____1564 =
                                       let uu____1565 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Basic.goal_ty in
                                       FStar_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu____1565 in
                                     failwith uu____1564
                                 | Some phi -> phi in
                               ((let uu____1568 =
                                   let uu____1569 =
                                     FStar_TypeChecker_Rel.teq_nosmt
                                       g.FStar_Tactics_Basic.context
                                       g.FStar_Tactics_Basic.witness
                                       FStar_Syntax_Const.exp_unit in
                                   Prims.op_Negation uu____1569 in
                                 if uu____1568
                                 then
                                   let uu____1570 =
                                     let uu____1571 =
                                       FStar_Syntax_Print.term_to_string
                                         g.FStar_Tactics_Basic.witness in
                                     FStar_Util.format1
                                       "Irrelevant tactic witness does not unify with (): %s"
                                       uu____1571 in
                                   failwith uu____1570
                                 else
                                   (let uu____1573 = FStar_ST.read tacdbg in
                                    if uu____1573
                                    then
                                      let uu____1576 =
                                        FStar_Util.string_of_int n1 in
                                      let uu____1577 =
                                        FStar_Tactics_Basic.goal_to_string g in
                                      FStar_Util.print2 "Got goal #%s: %s\n"
                                        uu____1576 uu____1577
                                    else ()));
                                (let gt' =
                                   let uu____1580 =
                                     let uu____1581 =
                                       FStar_Util.string_of_int n1 in
                                     Prims.strcat "Could not prove goal #"
                                       uu____1581 in
                                   FStar_TypeChecker_Util.label uu____1580
                                     FStar_Range.dummyRange phi in
                                 ((n1 + (Prims.parse_int "1")),
                                   (((g.FStar_Tactics_Basic.context), gt') ::
                                   gs1))))) s gs in
                  let uu____1587 = s1 in
                  match uu____1587 with
                  | (uu____1596,gs1) -> (env2, t') :: gs1))))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____1610 =
        let uu____1611 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational None in
        FStar_Syntax_Syntax.fv_to_tm uu____1611 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____1610 [FStar_Syntax_Syntax.U_zero] in
    let uu____1612 =
      let uu____1613 =
        let uu____1614 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____1615 =
          let uu____1617 = FStar_Syntax_Syntax.as_arg a in [uu____1617] in
        uu____1614 :: uu____1615 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____1613 in
    uu____1612 None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        let ps = FStar_Tactics_Basic.proofstate_of_goal_ty env typ in
        let w =
          let uu____1633 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
          uu____1633.FStar_Tactics_Basic.witness in
        let r =
          try
            let uu____1639 =
              let uu____1641 = reify_tactic tau in
              unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____1641 in
            FStar_Tactics_Basic.run uu____1639 ps
          with
          | FStar_Tactics_Basic.TacFailure s ->
              FStar_Tactics_Basic.Failed ((Prims.strcat "EXCEPTION: " s), ps) in
        match r with
        | FStar_Tactics_Basic.Success (uu____1645,ps1) ->
            ((let uu____1648 = FStar_ST.read tacdbg in
              if uu____1648
              then
                let uu____1651 = FStar_Syntax_Print.term_to_string w in
                FStar_Util.print1 "Tactic generated proofterm %s\n"
                  uu____1651
              else ());
             w)
        | FStar_Tactics_Basic.Failed (s,ps1) ->
            ((let uu____1656 = FStar_Util.format1 "user tactic failed: %s" s in
              FStar_Errors.err typ.FStar_Syntax_Syntax.pos uu____1656);
             failwith "aborting")