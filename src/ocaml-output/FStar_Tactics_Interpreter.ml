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
          mktac2 "__trytac" (fun uu____574  -> FStar_Tactics_Basic.trytac)
            (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
            (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit1)
            t_unit1 in
        let uu____578 =
          let uu____580 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____583 =
            let uu____585 =
              mktac1 "__norm" FStar_Tactics_Basic.norm
                (FStar_Reflection_Basic.unembed_list
                   FStar_Reflection_Basic.unembed_norm_step)
                FStar_Reflection_Basic.embed_unit t_unit1 in
            let uu____587 =
              let uu____589 =
                mktac0 "__revert" FStar_Tactics_Basic.revert
                  FStar_Reflection_Basic.embed_unit t_unit1 in
              let uu____590 =
                let uu____592 =
                  mktac0 "__clear" FStar_Tactics_Basic.clear
                    FStar_Reflection_Basic.embed_unit t_unit1 in
                let uu____593 =
                  let uu____595 =
                    mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Reflection_Basic.embed_unit t_unit1 in
                  let uu____596 =
                    let uu____598 =
                      mktac0 "__smt" FStar_Tactics_Basic.smt
                        FStar_Reflection_Basic.embed_unit t_unit1 in
                    let uu____599 =
                      let uu____601 =
                        mktac1 "__exact" FStar_Tactics_Basic.exact
                          FStar_Reflection_Basic.unembed_term
                          FStar_Reflection_Basic.embed_unit t_unit1 in
                      let uu____602 =
                        let uu____604 =
                          mktac1 "__apply" FStar_Tactics_Basic.apply
                            FStar_Reflection_Basic.unembed_term
                            FStar_Reflection_Basic.embed_unit t_unit1 in
                        let uu____605 =
                          let uu____607 =
                            mktac1 "__apply_lemma"
                              FStar_Tactics_Basic.apply_lemma
                              FStar_Reflection_Basic.unembed_term
                              FStar_Reflection_Basic.embed_unit t_unit1 in
                          let uu____608 =
                            let uu____610 =
                              mktac1 "__focus"
                                FStar_Tactics_Basic.focus_cur_goal
                                (unembed_tactic_0
                                   FStar_Reflection_Basic.unembed_unit)
                                FStar_Reflection_Basic.embed_unit t_unit1 in
                            let uu____612 =
                              let uu____614 =
                                mktac2 "__seq" FStar_Tactics_Basic.seq
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  (unembed_tactic_0
                                     FStar_Reflection_Basic.unembed_unit)
                                  FStar_Reflection_Basic.embed_unit t_unit1 in
                              let uu____617 =
                                let uu____619 =
                                  mktac1 "__prune" FStar_Tactics_Basic.prune
                                    FStar_Reflection_Basic.unembed_string
                                    FStar_Reflection_Basic.embed_unit t_unit1 in
                                let uu____620 =
                                  let uu____622 =
                                    mktac1 "__addns"
                                      FStar_Tactics_Basic.addns
                                      FStar_Reflection_Basic.unembed_string
                                      FStar_Reflection_Basic.embed_unit
                                      t_unit1 in
                                  let uu____623 =
                                    let uu____625 =
                                      mktac1 "__print"
                                        (fun x  ->
                                           FStar_Tactics_Basic.tacprint x;
                                           FStar_Tactics_Basic.ret ())
                                        FStar_Reflection_Basic.unembed_string
                                        FStar_Reflection_Basic.embed_unit
                                        t_unit1 in
                                    let uu____628 =
                                      let uu____630 =
                                        mktac1 "__dump"
                                          FStar_Tactics_Basic.print_proof_state
                                          FStar_Reflection_Basic.unembed_string
                                          FStar_Reflection_Basic.embed_unit
                                          t_unit1 in
                                      let uu____631 =
                                        let uu____633 =
                                          mktac1 "__dump1"
                                            FStar_Tactics_Basic.print_proof_state1
                                            FStar_Reflection_Basic.unembed_string
                                            FStar_Reflection_Basic.embed_unit
                                            t_unit1 in
                                        let uu____634 =
                                          let uu____636 =
                                            mktac1 "__pointwise"
                                              FStar_Tactics_Basic.pointwise
                                              (unembed_tactic_0
                                                 FStar_Reflection_Basic.unembed_unit)
                                              FStar_Reflection_Basic.embed_unit
                                              t_unit1 in
                                          let uu____638 =
                                            let uu____640 =
                                              mktac0 "__trefl"
                                                FStar_Tactics_Basic.trefl
                                                FStar_Reflection_Basic.embed_unit
                                                t_unit1 in
                                            let uu____641 =
                                              let uu____643 =
                                                mktac0 "__later"
                                                  FStar_Tactics_Basic.later
                                                  FStar_Reflection_Basic.embed_unit
                                                  t_unit1 in
                                              let uu____644 =
                                                let uu____646 =
                                                  mktac0 "__flip"
                                                    FStar_Tactics_Basic.flip
                                                    FStar_Reflection_Basic.embed_unit
                                                    t_unit1 in
                                                let uu____647 =
                                                  let uu____649 =
                                                    mktac0 "__qed"
                                                      FStar_Tactics_Basic.qed
                                                      FStar_Reflection_Basic.embed_unit
                                                      t_unit1 in
                                                  let uu____650 =
                                                    let uu____652 =
                                                      let uu____653 =
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
                                                        uu____653 in
                                                    let uu____656 =
                                                      let uu____658 =
                                                        mk_refl
                                                          ["Syntax";
                                                          "__binders_of_env"]
                                                          (Prims.parse_int
                                                             "1")
                                                          binders_of_env_int in
                                                      [uu____658] in
                                                    uu____652 :: uu____656 in
                                                  uu____649 :: uu____650 in
                                                uu____646 :: uu____647 in
                                              uu____643 :: uu____644 in
                                            uu____640 :: uu____641 in
                                          uu____636 :: uu____638 in
                                        uu____633 :: uu____634 in
                                      uu____630 :: uu____631 in
                                    uu____625 :: uu____628 in
                                  uu____622 :: uu____623 in
                                uu____619 :: uu____620 in
                              uu____614 :: uu____617 in
                            uu____610 :: uu____612 in
                          uu____607 :: uu____608 in
                        uu____604 :: uu____605 in
                      uu____601 :: uu____602 in
                    uu____598 :: uu____599 in
                  uu____595 :: uu____596 in
                uu____592 :: uu____593 in
              uu____589 :: uu____590 in
            uu____585 :: uu____587 in
          uu____580 :: uu____583 in
        uu____571 :: uu____578 in
      uu____568 :: uu____569 in
    FStar_List.append uu____566
      FStar_Reflection_Interpreter.reflection_primops
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____667 =
           let uu____668 =
             let uu____669 =
               let uu____670 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals),
                     (proof_state.FStar_Tactics_Basic.smt_goals)) in
               FStar_Syntax_Syntax.as_arg uu____670 in
             [uu____669] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____668 in
         uu____667 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____679 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____684  ->
              let uu____685 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____685) in
       FStar_Tactics_Basic.bind uu____679
         (fun uu____686  ->
            let result =
              let uu____688 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____688 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____690 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____695  ->
                   let uu____696 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____696) in
            FStar_Tactics_Basic.bind uu____690
              (fun uu____697  ->
                 let uu____698 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____698 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____725  ->
                          let uu____726 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____726
                            (fun uu____728  ->
                               let uu____729 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____729
                                 (fun uu____731  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____751  ->
                          let uu____752 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____752
                            (fun uu____754  ->
                               let uu____755 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____755
                                 (fun uu____757  ->
                                    FStar_Tactics_Basic.fail msg))))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____761 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____765 -> false
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
        let uu____784 = FStar_Syntax_Util.head_and_args t in
        match uu____784 with
        | (hd1,args) ->
            let uu____813 =
              let uu____821 =
                let uu____822 = FStar_Syntax_Util.un_uinst hd1 in
                uu____822.FStar_Syntax_Syntax.n in
              (uu____821, args) in
            (match uu____813 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____835)::(tactic,uu____837)::(assertion,uu____839)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____878)::(tactic,uu____880)::(assertion,uu____882)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let ps =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 let w =
                   let uu____918 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
                   uu____918.FStar_Tactics_Basic.witness in
                 let r =
                   try
                     let uu____924 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     FStar_Tactics_Basic.run uu____924 ps
                   with
                   | FStar_Tactics_Basic.TacFailure s ->
                       FStar_Tactics_Basic.Failed
                         ((Prims.strcat "EXCEPTION: " s), ps) in
                 (match r with
                  | FStar_Tactics_Basic.Success (uu____932,ps1) ->
                      ((let uu____935 = FStar_ST.read tacdbg in
                        if uu____935
                        then
                          let uu____938 = FStar_Syntax_Print.term_to_string w in
                          FStar_Util.print1 "Tactic generated proofterm %s\n"
                            uu____938
                        else ());
                       (FStar_Syntax_Util.t_true,
                         (FStar_List.append ps1.FStar_Tactics_Basic.goals
                            ps1.FStar_Tactics_Basic.smt_goals)))
                  | FStar_Tactics_Basic.Failed (s,ps1) ->
                      raise
                        (FStar_Errors.Error
                           ((Prims.strcat "user tactic failed: \""
                               (Prims.strcat s "\"")),
                             (tactic.FStar_Syntax_Syntax.pos))))
             | uu____946 -> (t, []))
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
          let uu____994 =
            let uu____998 =
              let uu____999 = FStar_Syntax_Subst.compress t in
              uu____999.FStar_Syntax_Syntax.n in
            match uu____998 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1011 = traverse f pol e t1 in
                (match uu____1011 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1029 = traverse f pol e t1 in
                (match uu____1029 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1042;
                   FStar_Syntax_Syntax.pos = uu____1043;
                   FStar_Syntax_Syntax.vars = uu____1044;_},(p,uu____1046)::
                 (q,uu____1048)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p in
                let uu____1079 =
                  let uu____1083 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1083 p in
                (match uu____1079 with
                 | (p',gs) ->
                     let uu____1091 =
                       let uu____1095 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1095 q in
                     (match uu____1091 with
                      | (q',gs1) ->
                          let uu____1103 =
                            let uu____1104 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1104.FStar_Syntax_Syntax.n in
                          (uu____1103, gs1)))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1124 = traverse f pol e hd1 in
                (match uu____1124 with
                 | (hd',gs1) ->
                     let uu____1135 =
                       FStar_List.fold_right
                         (fun uu____1150  ->
                            fun uu____1151  ->
                              match (uu____1150, uu____1151) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1194 = traverse f pol e a in
                                  (match uu____1194 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1135 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1262 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1262 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1271 = traverse f pol e' topen in
                     (match uu____1271 with
                      | (topen',gs) ->
                          let uu____1282 =
                            let uu____1283 =
                              FStar_Syntax_Util.abs bs1 topen' k in
                            uu____1283.FStar_Syntax_Syntax.n in
                          (uu____1282, gs)))
            | x -> (x, []) in
          match uu____994 with
          | (tn',gs) ->
              let t' =
                let uu___111_1299 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___111_1299.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___111_1299.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___111_1299.FStar_Syntax_Syntax.vars)
                } in
              let uu____1304 = f pol e t' in
              (match uu____1304 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1329 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1329);
      (let uu____1333 = FStar_ST.read tacdbg in
       if uu____1333
       then
         let uu____1336 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1336
       else ());
      (let uu____1338 = FStar_TypeChecker_Env.clear_expected_typ env in
       match uu____1338 with
       | (env1,uu____1346) ->
           let env2 =
             let uu___112_1350 = env1 in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___112_1350.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___112_1350.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___112_1350.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___112_1350.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___112_1350.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___112_1350.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___112_1350.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___112_1350.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___112_1350.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp = false;
               FStar_TypeChecker_Env.effects =
                 (uu___112_1350.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___112_1350.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___112_1350.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___112_1350.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___112_1350.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___112_1350.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___112_1350.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___112_1350.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___112_1350.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___112_1350.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.type_of =
                 (uu___112_1350.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___112_1350.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___112_1350.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___112_1350.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___112_1350.FStar_TypeChecker_Env.proof_ns)
             } in
           let initial = ((Prims.parse_int "1"), []) in
           let uu____1362 = traverse by_tactic_interp Pos env2 goal in
           (match uu____1362 with
            | (t',gs) ->
                ((let uu____1374 = FStar_ST.read tacdbg in
                  if uu____1374
                  then
                    let uu____1377 =
                      let uu____1378 = FStar_TypeChecker_Env.all_binders env2 in
                      FStar_All.pipe_right uu____1378
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu____1379 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                      uu____1377 uu____1379
                  else ());
                 (let s = initial in
                  let s1 =
                    FStar_List.fold_left
                      (fun uu____1398  ->
                         fun g  ->
                           match uu____1398 with
                           | (n1,gs1) ->
                               let typ =
                                 FStar_TypeChecker_Normalize.normalize []
                                   g.FStar_Tactics_Basic.context
                                   g.FStar_Tactics_Basic.goal_ty in
                               let phi =
                                 let uu____1422 =
                                   FStar_Syntax_Util.un_squash typ in
                                 match uu____1422 with
                                 | Some t -> t
                                 | None  ->
                                     let uu____1435 =
                                       let uu____1436 =
                                         FStar_Syntax_Print.term_to_string
                                           typ in
                                       FStar_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu____1436 in
                                     failwith uu____1435 in
                               ((let uu____1440 = FStar_ST.read tacdbg in
                                 if uu____1440
                                 then
                                   let uu____1443 =
                                     FStar_Util.string_of_int n1 in
                                   let uu____1444 =
                                     FStar_Tactics_Basic.goal_to_string g in
                                   FStar_Util.print2 "Got goal #%s: %s\n"
                                     uu____1443 uu____1444
                                 else ());
                                (let gt' =
                                   let uu____1447 =
                                     let uu____1448 =
                                       FStar_Util.string_of_int n1 in
                                     Prims.strcat "Could not prove goal #"
                                       uu____1448 in
                                   FStar_TypeChecker_Util.label uu____1447
                                     FStar_Range.dummyRange phi in
                                 ((n1 + (Prims.parse_int "1")),
                                   (((g.FStar_Tactics_Basic.context), gt') ::
                                   gs1))))) s gs in
                  let uu____1454 = s1 in
                  match uu____1454 with
                  | (uu____1463,gs1) -> (env2, t') :: gs1))))