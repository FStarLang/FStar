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
              let uu___109_73 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_73.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_73.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_73.FStar_Tactics_Basic.all_implicits);
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
              let uu___110_173 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_173.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_173.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_173.FStar_Tactics_Basic.all_implicits);
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
              let uu___111_306 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___111_306.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___111_306.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___111_306.FStar_Tactics_Basic.all_implicits);
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
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____326 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____326);
      {
        FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
        FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
        FStar_TypeChecker_Normalize.strong_reduction_ok =
          (s.FStar_Tactics_Native.strong_reduction_ok);
        FStar_TypeChecker_Normalize.interpretation =
          ((fun _rng  -> fun args  -> s.FStar_Tactics_Native.tactic ps args))
      }
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
    let native_tactics = FStar_Tactics_Native.list_all () in
    let native_tactics_steps =
      FStar_List.map (step_from_native_step ps) native_tactics in
    (let uu____382 =
       FStar_All.pipe_left FStar_Util.string_of_int
         (FStar_List.length native_tactics) in
     FStar_Util.print1 "Loaded %s native tactics\n" uu____382);
    (let mk_refl nm arity interpretation =
       let nm1 = FStar_Reflection_Data.fstar_refl_lid nm in
       {
         FStar_TypeChecker_Normalize.name = nm1;
         FStar_TypeChecker_Normalize.arity = arity;
         FStar_TypeChecker_Normalize.strong_reduction_ok = false;
         FStar_TypeChecker_Normalize.interpretation =
           (fun _rng  -> fun args  -> interpretation nm1 args)
       } in
     let mktac0 name f e_a ta =
       mk1 name (Prims.parse_int "1")
         (mk_tactic_interpretation_0 ps f e_a ta) in
     let mktac1 name f u_a e_b tb =
       mk1 name (Prims.parse_int "2")
         (mk_tactic_interpretation_1 ps f u_a e_b tb) in
     let mktac2 name f u_a u_b e_c tc =
       mk1 name (Prims.parse_int "3")
         (mk_tactic_interpretation_2 ps f u_a u_b e_c tc) in
     let binders_of_env_int nm args =
       match args with
       | (e,uu____570)::[] ->
           let uu____575 =
             let uu____576 =
               let uu____578 = FStar_Tactics_Embedding.unembed_env ps e in
               FStar_TypeChecker_Env.all_binders uu____578 in
             FStar_Reflection_Basic.embed_binders uu____576 in
           Some uu____575
       | uu____579 ->
           let uu____583 =
             let uu____584 = FStar_Ident.string_of_lid nm in
             let uu____585 = FStar_Syntax_Print.args_to_string args in
             FStar_Util.format2 "Unexpected application %s %s" uu____584
               uu____585 in
           failwith uu____583 in
     let uu____587 =
       let uu____589 =
         mktac0 "__trivial" FStar_Tactics_Basic.trivial
           FStar_Reflection_Basic.embed_unit t_unit in
       let uu____590 =
         let uu____592 =
           mktac2 "__trytac" (fun uu____595  -> FStar_Tactics_Basic.trytac)
             (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
             (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit)
             t_unit in
         let uu____599 =
           let uu____601 =
             mktac0 "__intro" FStar_Tactics_Basic.intro
               FStar_Reflection_Basic.embed_binder
               FStar_Reflection_Data.fstar_refl_binder in
           let uu____604 =
             let uu____606 =
               mktac1 "__norm" FStar_Tactics_Basic.norm
                 (FStar_Reflection_Basic.unembed_list
                    FStar_Reflection_Basic.unembed_norm_step)
                 FStar_Reflection_Basic.embed_unit t_unit in
             let uu____608 =
               let uu____610 =
                 mktac0 "__revert" FStar_Tactics_Basic.revert
                   FStar_Reflection_Basic.embed_unit t_unit in
               let uu____611 =
                 let uu____613 =
                   mktac0 "__clear" FStar_Tactics_Basic.clear
                     FStar_Reflection_Basic.embed_unit t_unit in
                 let uu____614 =
                   let uu____616 =
                     mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                       FStar_Reflection_Basic.unembed_binder
                       FStar_Reflection_Basic.embed_unit t_unit in
                   let uu____617 =
                     let uu____619 =
                       mktac0 "__smt" FStar_Tactics_Basic.smt
                         FStar_Reflection_Basic.embed_unit t_unit in
                     let uu____620 =
                       let uu____622 =
                         mktac1 "__exact" FStar_Tactics_Basic.exact
                           FStar_Reflection_Basic.unembed_term
                           FStar_Reflection_Basic.embed_unit t_unit in
                       let uu____623 =
                         let uu____625 =
                           mktac1 "__exact_lemma"
                             FStar_Tactics_Basic.exact_lemma
                             FStar_Reflection_Basic.unembed_term
                             FStar_Reflection_Basic.embed_unit t_unit in
                         let uu____626 =
                           let uu____628 =
                             mktac1 "__apply" FStar_Tactics_Basic.apply
                               FStar_Reflection_Basic.unembed_term
                               FStar_Reflection_Basic.embed_unit t_unit in
                           let uu____629 =
                             let uu____631 =
                               mktac1 "__apply_lemma"
                                 FStar_Tactics_Basic.apply_lemma
                                 FStar_Reflection_Basic.unembed_term
                                 FStar_Reflection_Basic.embed_unit t_unit in
                             let uu____632 =
                               let uu____634 =
                                 mktac1 "__focus"
                                   FStar_Tactics_Basic.focus_cur_goal
                                   (unembed_tactic_0
                                      FStar_Reflection_Basic.unembed_unit)
                                   FStar_Reflection_Basic.embed_unit t_unit in
                               let uu____636 =
                                 let uu____638 =
                                   mktac2 "__seq" FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Reflection_Basic.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Reflection_Basic.unembed_unit)
                                     FStar_Reflection_Basic.embed_unit t_unit in
                                 let uu____641 =
                                   let uu____643 =
                                     mktac1 "__prune"
                                       FStar_Tactics_Basic.prune
                                       FStar_Reflection_Basic.unembed_string
                                       FStar_Reflection_Basic.embed_unit
                                       t_unit in
                                   let uu____644 =
                                     let uu____646 =
                                       mktac1 "__addns"
                                         FStar_Tactics_Basic.addns
                                         FStar_Reflection_Basic.unembed_string
                                         FStar_Reflection_Basic.embed_unit
                                         t_unit in
                                     let uu____647 =
                                       let uu____649 =
                                         mktac1 "__print"
                                           (fun x  ->
                                              FStar_Tactics_Basic.tacprint x;
                                              FStar_Tactics_Basic.ret ())
                                           FStar_Reflection_Basic.unembed_string
                                           FStar_Reflection_Basic.embed_unit
                                           t_unit in
                                       let uu____652 =
                                         let uu____654 =
                                           mktac1 "__dump"
                                             FStar_Tactics_Basic.print_proof_state
                                             FStar_Reflection_Basic.unembed_string
                                             FStar_Reflection_Basic.embed_unit
                                             t_unit in
                                         let uu____655 =
                                           let uu____657 =
                                             mktac1 "__dump1"
                                               FStar_Tactics_Basic.print_proof_state1
                                               FStar_Reflection_Basic.unembed_string
                                               FStar_Reflection_Basic.embed_unit
                                               t_unit in
                                           let uu____658 =
                                             let uu____660 =
                                               mktac1 "__pointwise"
                                                 FStar_Tactics_Basic.pointwise
                                                 (unembed_tactic_0
                                                    FStar_Reflection_Basic.unembed_unit)
                                                 FStar_Reflection_Basic.embed_unit
                                                 t_unit in
                                             let uu____662 =
                                               let uu____664 =
                                                 mktac0 "__trefl"
                                                   FStar_Tactics_Basic.trefl
                                                   FStar_Reflection_Basic.embed_unit
                                                   t_unit in
                                               let uu____665 =
                                                 let uu____667 =
                                                   mktac0 "__later"
                                                     FStar_Tactics_Basic.later
                                                     FStar_Reflection_Basic.embed_unit
                                                     t_unit in
                                                 let uu____668 =
                                                   let uu____670 =
                                                     mktac0 "__flip"
                                                       FStar_Tactics_Basic.flip
                                                       FStar_Reflection_Basic.embed_unit
                                                       t_unit in
                                                   let uu____671 =
                                                     let uu____673 =
                                                       mktac0 "__qed"
                                                         FStar_Tactics_Basic.qed
                                                         FStar_Reflection_Basic.embed_unit
                                                         t_unit in
                                                     let uu____674 =
                                                       let uu____676 =
                                                         let uu____677 =
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
                                                           uu____677 in
                                                       let uu____680 =
                                                         let uu____682 =
                                                           mk_refl
                                                             ["Syntax";
                                                             "__binders_of_env"]
                                                             (Prims.parse_int
                                                                "1")
                                                             binders_of_env_int in
                                                         let uu____683 =
                                                           let uu____685 =
                                                             mktac0
                                                               "__cur_env"
                                                               FStar_Tactics_Basic.cur_env
                                                               (FStar_Tactics_Embedding.embed_env
                                                                  ps)
                                                               FStar_Reflection_Data.fstar_refl_env in
                                                           let uu____686 =
                                                             let uu____688 =
                                                               mktac0
                                                                 "__cur_goal"
                                                                 FStar_Tactics_Basic.cur_goal'
                                                                 FStar_Reflection_Basic.embed_term
                                                                 FStar_Reflection_Data.fstar_refl_term in
                                                             let uu____689 =
                                                               let uu____691
                                                                 =
                                                                 mktac0
                                                                   "__cur_witness"
                                                                   FStar_Tactics_Basic.cur_witness
                                                                   FStar_Reflection_Basic.embed_term
                                                                   FStar_Reflection_Data.fstar_refl_term in
                                                               [uu____691] in
                                                             uu____688 ::
                                                               uu____689 in
                                                           uu____685 ::
                                                             uu____686 in
                                                         uu____682 ::
                                                           uu____683 in
                                                       uu____676 :: uu____680 in
                                                     uu____673 :: uu____674 in
                                                   uu____670 :: uu____671 in
                                                 uu____667 :: uu____668 in
                                               uu____664 :: uu____665 in
                                             uu____660 :: uu____662 in
                                           uu____657 :: uu____658 in
                                         uu____654 :: uu____655 in
                                       uu____649 :: uu____652 in
                                     uu____646 :: uu____647 in
                                   uu____643 :: uu____644 in
                                 uu____638 :: uu____641 in
                               uu____634 :: uu____636 in
                             uu____631 :: uu____632 in
                           uu____628 :: uu____629 in
                         uu____625 :: uu____626 in
                       uu____622 :: uu____623 in
                     uu____619 :: uu____620 in
                   uu____616 :: uu____617 in
                 uu____613 :: uu____614 in
               uu____610 :: uu____611 in
             uu____606 :: uu____608 in
           uu____601 :: uu____604 in
         uu____592 :: uu____599 in
       uu____589 :: uu____590 in
     FStar_List.append uu____587
       (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
          native_tactics_steps))
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____700 =
           let uu____701 =
             let uu____702 =
               let uu____703 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals),
                     (proof_state.FStar_Tactics_Basic.smt_goals)) in
               FStar_Syntax_Syntax.as_arg uu____703 in
             [uu____702] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____701 in
         uu____700 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.UnfoldTac;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____712 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____717  ->
              let uu____718 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____718) in
       FStar_Tactics_Basic.bind uu____712
         (fun uu____719  ->
            let result =
              let uu____721 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____721 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____723 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____728  ->
                   let uu____729 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____729) in
            FStar_Tactics_Basic.bind uu____723
              (fun uu____730  ->
                 let uu____731 =
                   FStar_Tactics_Embedding.unembed_result proof_state result
                     unembed_b in
                 match uu____731 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____758  ->
                          let uu____759 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____759
                            (fun uu____761  ->
                               let uu____762 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____762
                                 (fun uu____764  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____784  ->
                          let uu____785 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____785
                            (fun uu____787  ->
                               let uu____788 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____788
                                 (fun uu____790  ->
                                    FStar_Tactics_Basic.fail msg))))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____794 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____798 -> false
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
        let uu____817 = FStar_Syntax_Util.head_and_args t in
        match uu____817 with
        | (hd1,args) ->
            let uu____846 =
              let uu____854 =
                let uu____855 = FStar_Syntax_Util.un_uinst hd1 in
                uu____855.FStar_Syntax_Syntax.n in
              (uu____854, args) in
            (match uu____846 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____868)::(tactic,uu____870)::(assertion,uu____872)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____911)::(tactic,uu____913)::(assertion,uu____915)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let ps =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 let w =
                   let uu____951 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
                   uu____951.FStar_Tactics_Basic.witness in
                 let r =
                   try
                     let uu____957 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     FStar_Tactics_Basic.run uu____957 ps
                   with
                   | FStar_Tactics_Basic.TacFailure s ->
                       FStar_Tactics_Basic.Failed
                         ((Prims.strcat "EXCEPTION: " s), ps) in
                 (match r with
                  | FStar_Tactics_Basic.Success (uu____965,ps1) ->
                      ((let uu____968 = FStar_ST.read tacdbg in
                        if uu____968
                        then
                          let uu____971 = FStar_Syntax_Print.term_to_string w in
                          FStar_Util.print1 "Tactic generated proofterm %s\n"
                            uu____971
                        else ());
                       (FStar_Syntax_Util.t_true,
                         (FStar_List.append ps1.FStar_Tactics_Basic.goals
                            ps1.FStar_Tactics_Basic.smt_goals)))
                  | FStar_Tactics_Basic.Failed (s,ps1) ->
                      ((let uu____977 =
                          FStar_Util.format1 "user tactic failed: %s" s in
                        FStar_Errors.err assertion.FStar_Syntax_Syntax.pos
                          uu____977);
                       (t, [])))
             | uu____979 -> (t, []))
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
          let uu____1027 =
            let uu____1031 =
              let uu____1032 = FStar_Syntax_Subst.compress t in
              uu____1032.FStar_Syntax_Syntax.n in
            match uu____1031 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1044 = traverse f pol e t1 in
                (match uu____1044 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1062 = traverse f pol e t1 in
                (match uu____1062 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1075;
                   FStar_Syntax_Syntax.pos = uu____1076;
                   FStar_Syntax_Syntax.vars = uu____1077;_},(p,uu____1079)::
                 (q,uu____1081)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p in
                let uu____1112 =
                  let uu____1116 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1116 p in
                (match uu____1112 with
                 | (p',gs1) ->
                     let uu____1124 =
                       let uu____1128 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1128 q in
                     (match uu____1124 with
                      | (q',gs2) ->
                          let uu____1136 =
                            let uu____1137 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1137.FStar_Syntax_Syntax.n in
                          (uu____1136, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1157 = traverse f pol e hd1 in
                (match uu____1157 with
                 | (hd',gs1) ->
                     let uu____1168 =
                       FStar_List.fold_right
                         (fun uu____1183  ->
                            fun uu____1184  ->
                              match (uu____1183, uu____1184) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1227 = traverse f pol e a in
                                  (match uu____1227 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1168 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1285 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1285 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1294 =
                       let uu____1302 =
                         FStar_List.map
                           (fun uu____1316  ->
                              match uu____1316 with
                              | (bv,aq) ->
                                  let uu____1326 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____1326 with
                                   | (s',gs) ->
                                       (((let uu___114_1342 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___114_1342.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___114_1342.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____1302 in
                     (match uu____1294 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____1376 = traverse f pol e' topen in
                          (match uu____1376 with
                           | (topen',gs2) ->
                               let uu____1387 =
                                 let uu____1388 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____1388.FStar_Syntax_Syntax.n in
                               (uu____1387, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____1027 with
          | (tn',gs) ->
              let t' =
                let uu___115_1404 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___115_1404.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___115_1404.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___115_1404.FStar_Syntax_Syntax.vars)
                } in
              let uu____1409 = f pol e t' in
              (match uu____1409 with
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
      let uu____1430 = FStar_Syntax_Util.un_squash tn in
      match uu____1430 with
      | Some t' -> Some t'
      | None  ->
          let uu____1444 = FStar_Syntax_Util.head_and_args tn in
          (match uu____1444 with
           | (hd1,uu____1456) ->
               let uu____1471 =
                 let uu____1472 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____1472.FStar_Syntax_Syntax.n in
               (match uu____1471 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid
                    -> Some t
                | uu____1477 -> None))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1491 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1491);
      (let uu____1495 = FStar_ST.read tacdbg in
       if uu____1495
       then
         let uu____1498 =
           let uu____1499 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____1499
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____1500 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____1498
           uu____1500
       else ());
      (let uu____1502 = FStar_TypeChecker_Env.clear_expected_typ env in
       match uu____1502 with
       | (env1,uu____1510) ->
           let env2 =
             let uu___116_1514 = env1 in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___116_1514.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___116_1514.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___116_1514.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___116_1514.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___116_1514.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___116_1514.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___116_1514.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___116_1514.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___116_1514.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp = false;
               FStar_TypeChecker_Env.effects =
                 (uu___116_1514.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___116_1514.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___116_1514.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___116_1514.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___116_1514.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___116_1514.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___116_1514.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___116_1514.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___116_1514.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___116_1514.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.type_of =
                 (uu___116_1514.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___116_1514.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___116_1514.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___116_1514.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___116_1514.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___116_1514.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___116_1514.FStar_TypeChecker_Env.is_native_tactic)
             } in
           let initial = ((Prims.parse_int "1"), []) in
           let uu____1526 = traverse by_tactic_interp Pos env2 goal in
           (match uu____1526 with
            | (t',gs) ->
                ((let uu____1538 = FStar_ST.read tacdbg in
                  if uu____1538
                  then
                    let uu____1541 =
                      let uu____1542 = FStar_TypeChecker_Env.all_binders env2 in
                      FStar_All.pipe_right uu____1542
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu____1543 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                      uu____1541 uu____1543
                  else ());
                 (let s = initial in
                  let s1 =
                    FStar_List.fold_left
                      (fun uu____1562  ->
                         fun g  ->
                           match uu____1562 with
                           | (n1,gs1) ->
                               let phi =
                                 let uu____1583 =
                                   getprop g.FStar_Tactics_Basic.context
                                     g.FStar_Tactics_Basic.goal_ty in
                                 match uu____1583 with
                                 | None  ->
                                     let uu____1585 =
                                       let uu____1586 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Basic.goal_ty in
                                       FStar_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu____1586 in
                                     failwith uu____1585
                                 | Some phi -> phi in
                               ((let uu____1589 =
                                   let uu____1590 =
                                     FStar_TypeChecker_Rel.teq_nosmt
                                       g.FStar_Tactics_Basic.context
                                       g.FStar_Tactics_Basic.witness
                                       FStar_Syntax_Const.exp_unit in
                                   Prims.op_Negation uu____1590 in
                                 if uu____1589
                                 then
                                   let uu____1591 =
                                     let uu____1592 =
                                       FStar_Syntax_Print.term_to_string
                                         g.FStar_Tactics_Basic.witness in
                                     FStar_Util.format1
                                       "Irrelevant tactic witness does not unify with (): %s"
                                       uu____1592 in
                                   failwith uu____1591
                                 else
                                   (let uu____1594 = FStar_ST.read tacdbg in
                                    if uu____1594
                                    then
                                      let uu____1597 =
                                        FStar_Util.string_of_int n1 in
                                      let uu____1598 =
                                        FStar_Tactics_Basic.goal_to_string g in
                                      FStar_Util.print2 "Got goal #%s: %s\n"
                                        uu____1597 uu____1598
                                    else ()));
                                (let gt' =
                                   let uu____1601 =
                                     let uu____1602 =
                                       FStar_Util.string_of_int n1 in
                                     Prims.strcat "Could not prove goal #"
                                       uu____1602 in
                                   FStar_TypeChecker_Util.label uu____1601
                                     FStar_Range.dummyRange phi in
                                 ((n1 + (Prims.parse_int "1")),
                                   (((g.FStar_Tactics_Basic.context), gt') ::
                                   gs1))))) s gs in
                  let uu____1608 = s1 in
                  match uu____1608 with
                  | (uu____1617,gs1) -> (env2, t') :: gs1))))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____1631 =
        let uu____1632 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational None in
        FStar_Syntax_Syntax.fv_to_tm uu____1632 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____1631 [FStar_Syntax_Syntax.U_zero] in
    let uu____1633 =
      let uu____1634 =
        let uu____1635 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____1636 =
          let uu____1638 = FStar_Syntax_Syntax.as_arg a in [uu____1638] in
        uu____1635 :: uu____1636 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____1634 in
    uu____1633 None a.FStar_Syntax_Syntax.pos
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
          let uu____1654 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
          uu____1654.FStar_Tactics_Basic.witness in
        let r =
          try
            let uu____1660 =
              let uu____1662 = reify_tactic tau in
              unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____1662 in
            FStar_Tactics_Basic.run uu____1660 ps
          with
          | FStar_Tactics_Basic.TacFailure s ->
              FStar_Tactics_Basic.Failed ((Prims.strcat "EXCEPTION: " s), ps) in
        match r with
        | FStar_Tactics_Basic.Success (uu____1666,ps1) ->
            ((let uu____1669 = FStar_ST.read tacdbg in
              if uu____1669
              then
                let uu____1672 = FStar_Syntax_Print.term_to_string w in
                FStar_Util.print1 "Tactic generated proofterm %s\n"
                  uu____1672
              else ());
             w)
        | FStar_Tactics_Basic.Failed (s,ps1) ->
            ((let uu____1677 = FStar_Util.format1 "user tactic failed: %s" s in
              FStar_Errors.err typ.FStar_Syntax_Syntax.pos uu____1677);
             failwith "aborting")