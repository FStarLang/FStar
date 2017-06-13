open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let t_unit:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  = FStar_TypeChecker_Common.t_unit
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____54)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____68  ->
            let uu____69 = FStar_Ident.string_of_lid nm in
            let uu____70 = FStar_Syntax_Print.args_to_string args in
            FStar_Util.print2 "Reached %s, args are: %s\n" uu____69 uu____70);
       (let uu____71 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____71 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_80 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_80.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_80.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_80.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____83 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____83))
  | uu____84 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____153)::(embedded_state,uu____155)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____177  ->
            let uu____178 = FStar_Ident.string_of_lid nm in
            let uu____179 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____178
              uu____179);
       (let uu____180 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____180 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_189 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_189.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_189.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_189.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____192 = let uu____194 = unembed_b b in t uu____194 in
              FStar_Tactics_Basic.run uu____192 ps1 in
            let uu____195 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_a t_a in
            Some uu____195))
  | uu____196 ->
      let uu____197 =
        let uu____198 = FStar_Ident.string_of_lid nm in
        let uu____199 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____198 uu____199 in
      failwith uu____197
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____287)::(b,uu____289)::(embedded_state,uu____291)::[] ->
      (FStar_Tactics_Basic.log ps
         (fun uu____321  ->
            let uu____322 = FStar_Ident.string_of_lid nm in
            let uu____323 = FStar_Syntax_Print.term_to_string embedded_state in
            FStar_Util.print2 "Reached %s, goals are: %s\n" uu____322
              uu____323);
       (let uu____324 =
          FStar_Tactics_Embedding.unembed_state ps embedded_state in
        match uu____324 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_333 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_333.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_333.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_333.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals
              } in
            let res =
              let uu____336 =
                let uu____338 = unembed_a a in
                let uu____339 = unembed_b b in t uu____338 uu____339 in
              FStar_Tactics_Basic.run uu____336 ps1 in
            let uu____340 =
              FStar_Tactics_Embedding.embed_result ps1 res embed_c t_c in
            Some uu____340))
  | uu____341 ->
      let uu____342 =
        let uu____343 = FStar_Ident.string_of_lid nm in
        let uu____344 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____343 uu____344 in
      failwith uu____342
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____355 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____355);
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
    (let uu____411 =
       FStar_All.pipe_left FStar_Util.string_of_int
         (FStar_List.length native_tactics) in
     FStar_Util.print1 "Loaded %s native tactics\n" uu____411);
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
       | (e,uu____601)::[] ->
           let uu____606 =
             let uu____607 =
               let uu____609 = FStar_Tactics_Embedding.unembed_env ps e in
               FStar_TypeChecker_Env.all_binders uu____609 in
             FStar_Reflection_Basic.embed_binders uu____607 in
           Some uu____606
       | uu____610 ->
           let uu____614 =
             let uu____615 = FStar_Ident.string_of_lid nm in
             let uu____616 = FStar_Syntax_Print.args_to_string args in
             FStar_Util.format2 "Unexpected application %s %s" uu____615
               uu____616 in
           failwith uu____614 in
     let uu____618 =
       let uu____620 =
         mktac0 "__trivial" FStar_Tactics_Basic.trivial
           FStar_Reflection_Basic.embed_unit t_unit in
       let uu____621 =
         let uu____623 =
           mktac2 "__trytac" (fun uu____626  -> FStar_Tactics_Basic.trytac)
             (fun t  -> t) (unembed_tactic_0 (fun t  -> t))
             (FStar_Reflection_Basic.embed_option (fun t  -> t) t_unit)
             t_unit in
         let uu____630 =
           let uu____632 =
             mktac0 "__intro" FStar_Tactics_Basic.intro
               FStar_Reflection_Basic.embed_binder
               FStar_Reflection_Data.fstar_refl_binder in
           let uu____635 =
             let uu____637 =
               mktac1 "__norm" FStar_Tactics_Basic.norm
                 (FStar_Reflection_Basic.unembed_list
                    FStar_Reflection_Basic.unembed_norm_step)
                 FStar_Reflection_Basic.embed_unit t_unit in
             let uu____639 =
               let uu____641 =
                 mktac0 "__revert" FStar_Tactics_Basic.revert
                   FStar_Reflection_Basic.embed_unit t_unit in
               let uu____642 =
                 let uu____644 =
                   mktac0 "__clear" FStar_Tactics_Basic.clear
                     FStar_Reflection_Basic.embed_unit t_unit in
                 let uu____645 =
                   let uu____647 =
                     mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                       FStar_Reflection_Basic.unembed_binder
                       FStar_Reflection_Basic.embed_unit t_unit in
                   let uu____648 =
                     let uu____650 =
                       mktac0 "__smt" FStar_Tactics_Basic.smt
                         FStar_Reflection_Basic.embed_unit t_unit in
                     let uu____651 =
                       let uu____653 =
                         mktac1 "__exact" FStar_Tactics_Basic.exact
                           FStar_Reflection_Basic.unembed_term
                           FStar_Reflection_Basic.embed_unit t_unit in
                       let uu____654 =
                         let uu____656 =
                           mktac1 "__exact_lemma"
                             FStar_Tactics_Basic.exact_lemma
                             FStar_Reflection_Basic.unembed_term
                             FStar_Reflection_Basic.embed_unit t_unit in
                         let uu____657 =
                           let uu____659 =
                             mktac1 "__apply" FStar_Tactics_Basic.apply
                               FStar_Reflection_Basic.unembed_term
                               FStar_Reflection_Basic.embed_unit t_unit in
                           let uu____660 =
                             let uu____662 =
                               mktac1 "__apply_lemma"
                                 FStar_Tactics_Basic.apply_lemma
                                 FStar_Reflection_Basic.unembed_term
                                 FStar_Reflection_Basic.embed_unit t_unit in
                             let uu____663 =
                               let uu____665 =
                                 mktac1 "__focus"
                                   FStar_Tactics_Basic.focus_cur_goal
                                   (unembed_tactic_0
                                      FStar_Reflection_Basic.unembed_unit)
                                   FStar_Reflection_Basic.embed_unit t_unit in
                               let uu____667 =
                                 let uu____669 =
                                   mktac2 "__seq" FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Reflection_Basic.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Reflection_Basic.unembed_unit)
                                     FStar_Reflection_Basic.embed_unit t_unit in
                                 let uu____672 =
                                   let uu____674 =
                                     mktac1 "__prune"
                                       FStar_Tactics_Basic.prune
                                       FStar_Reflection_Basic.unembed_string
                                       FStar_Reflection_Basic.embed_unit
                                       t_unit in
                                   let uu____675 =
                                     let uu____677 =
                                       mktac1 "__addns"
                                         FStar_Tactics_Basic.addns
                                         FStar_Reflection_Basic.unembed_string
                                         FStar_Reflection_Basic.embed_unit
                                         t_unit in
                                     let uu____678 =
                                       let uu____680 =
                                         mktac1 "__print"
                                           (fun x  ->
                                              FStar_Tactics_Basic.tacprint x;
                                              FStar_Tactics_Basic.ret ())
                                           FStar_Reflection_Basic.unembed_string
                                           FStar_Reflection_Basic.embed_unit
                                           t_unit in
                                       let uu____683 =
                                         let uu____685 =
                                           mktac1 "__dump"
                                             FStar_Tactics_Basic.print_proof_state
                                             FStar_Reflection_Basic.unembed_string
                                             FStar_Reflection_Basic.embed_unit
                                             t_unit in
                                         let uu____686 =
                                           let uu____688 =
                                             mktac1 "__dump1"
                                               FStar_Tactics_Basic.print_proof_state1
                                               FStar_Reflection_Basic.unembed_string
                                               FStar_Reflection_Basic.embed_unit
                                               t_unit in
                                           let uu____689 =
                                             let uu____691 =
                                               mktac1 "__pointwise"
                                                 FStar_Tactics_Basic.pointwise
                                                 (unembed_tactic_0
                                                    FStar_Reflection_Basic.unembed_unit)
                                                 FStar_Reflection_Basic.embed_unit
                                                 t_unit in
                                             let uu____693 =
                                               let uu____695 =
                                                 mktac0 "__trefl"
                                                   FStar_Tactics_Basic.trefl
                                                   FStar_Reflection_Basic.embed_unit
                                                   t_unit in
                                               let uu____696 =
                                                 let uu____698 =
                                                   mktac0 "__later"
                                                     FStar_Tactics_Basic.later
                                                     FStar_Reflection_Basic.embed_unit
                                                     t_unit in
                                                 let uu____699 =
                                                   let uu____701 =
                                                     mktac0 "__flip"
                                                       FStar_Tactics_Basic.flip
                                                       FStar_Reflection_Basic.embed_unit
                                                       t_unit in
                                                   let uu____702 =
                                                     let uu____704 =
                                                       mktac0 "__qed"
                                                         FStar_Tactics_Basic.qed
                                                         FStar_Reflection_Basic.embed_unit
                                                         t_unit in
                                                     let uu____705 =
                                                       let uu____707 =
                                                         let uu____708 =
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
                                                           uu____708 in
                                                       let uu____711 =
                                                         let uu____713 =
                                                           mk_refl
                                                             ["Syntax";
                                                             "__binders_of_env"]
                                                             (Prims.parse_int
                                                                "1")
                                                             binders_of_env_int in
                                                         [uu____713] in
                                                       uu____707 :: uu____711 in
                                                     uu____704 :: uu____705 in
                                                   uu____701 :: uu____702 in
                                                 uu____698 :: uu____699 in
                                               uu____695 :: uu____696 in
                                             uu____691 :: uu____693 in
                                           uu____688 :: uu____689 in
                                         uu____685 :: uu____686 in
                                       uu____680 :: uu____683 in
                                     uu____677 :: uu____678 in
                                   uu____674 :: uu____675 in
                                 uu____669 :: uu____672 in
                               uu____665 :: uu____667 in
                             uu____662 :: uu____663 in
                           uu____659 :: uu____660 in
                         uu____656 :: uu____657 in
                       uu____653 :: uu____654 in
                     uu____650 :: uu____651 in
                   uu____647 :: uu____648 in
                 uu____644 :: uu____645 in
               uu____641 :: uu____642 in
             uu____637 :: uu____639 in
           uu____632 :: uu____635 in
         uu____623 :: uu____630 in
       uu____620 :: uu____621 in
     FStar_List.append uu____618
       (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
          native_tactics_steps))
and unembed_tactic_0 : 'b. (FStar_Syntax_Syntax.term -> 'b) -> FStar_Syntax_Syntax.term -> 'b FStar_Tactics_Basic.tac =
fun unembed_b embedded_tac_b ->
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____722 =
           let uu____723 =
             let uu____724 =
               let uu____725 =
                 FStar_Tactics_Embedding.embed_state proof_state
                   ((proof_state.FStar_Tactics_Basic.goals),
                     (proof_state.FStar_Tactics_Basic.smt_goals)) in
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
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____780  ->
                          let uu____781 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____781
                            (fun uu____783  ->
                               let uu____784 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____784
                                 (fun uu____786  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss_all
                       (fun uu____806  ->
                          let uu____807 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____807
                            (fun uu____809  ->
                               let uu____810 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____810
                                 (fun uu____812  ->
                                    FStar_Tactics_Basic.fail msg))))))
type pol =
  | Pos
  | Neg
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____817 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____822 -> false
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
        let uu____845 = FStar_Syntax_Util.head_and_args t in
        match uu____845 with
        | (hd1,args) ->
            let uu____874 =
              let uu____882 =
                let uu____883 = FStar_Syntax_Util.un_uinst hd1 in
                uu____883.FStar_Syntax_Syntax.n in
              (uu____882, args) in
            (match uu____874 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____896)::(tactic,uu____898)::(assertion,uu____900)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Neg)
                 -> (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,uu____939)::(tactic,uu____941)::(assertion,uu____943)::[])
                 when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Tactics_Embedding.by_tactic_lid)
                   && (pol = Pos)
                 ->
                 let ps =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 let w =
                   let uu____979 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
                   uu____979.FStar_Tactics_Basic.witness in
                 let r =
                   try
                     let uu____985 =
                       unembed_tactic_0 FStar_Reflection_Basic.unembed_unit
                         tactic in
                     FStar_Tactics_Basic.run uu____985 ps
                   with
                   | FStar_Tactics_Basic.TacFailure s ->
                       FStar_Tactics_Basic.Failed
                         ((Prims.strcat "EXCEPTION: " s), ps) in
                 (match r with
                  | FStar_Tactics_Basic.Success (uu____993,ps1) ->
                      ((let uu____996 = FStar_ST.read tacdbg in
                        if uu____996
                        then
                          let uu____999 = FStar_Syntax_Print.term_to_string w in
                          FStar_Util.print1 "Tactic generated proofterm %s\n"
                            uu____999
                        else ());
                       (FStar_Syntax_Util.t_true,
                         (FStar_List.append ps1.FStar_Tactics_Basic.goals
                            ps1.FStar_Tactics_Basic.smt_goals)))
                  | FStar_Tactics_Basic.Failed (s,ps1) ->
                      ((let uu____1005 =
                          FStar_Util.format1 "user tactic failed: %s" s in
                        FStar_Errors.err assertion.FStar_Syntax_Syntax.pos
                          uu____1005);
                       (t, [])))
             | uu____1007 -> (t, []))
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
          let uu____1059 =
            let uu____1063 =
              let uu____1064 = FStar_Syntax_Subst.compress t in
              uu____1064.FStar_Syntax_Syntax.n in
            match uu____1063 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____1076 = traverse f pol e t1 in
                (match uu____1076 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____1094 = traverse f pol e t1 in
                (match uu____1094 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____1107;
                   FStar_Syntax_Syntax.pos = uu____1108;
                   FStar_Syntax_Syntax.vars = uu____1109;_},(p,uu____1111)::
                 (q,uu____1113)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid
                ->
                let x = FStar_Syntax_Syntax.new_bv None p in
                let uu____1144 =
                  let uu____1148 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f (flip pol) uu____1148 p in
                (match uu____1144 with
                 | (p',gs1) ->
                     let uu____1156 =
                       let uu____1160 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____1160 q in
                     (match uu____1156 with
                      | (q',gs2) ->
                          let uu____1168 =
                            let uu____1169 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____1169.FStar_Syntax_Syntax.n in
                          (uu____1168, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____1189 = traverse f pol e hd1 in
                (match uu____1189 with
                 | (hd',gs1) ->
                     let uu____1200 =
                       FStar_List.fold_right
                         (fun uu____1215  ->
                            fun uu____1216  ->
                              match (uu____1215, uu____1216) with
                              | ((a,q),(as',gs)) ->
                                  let uu____1259 = traverse f pol e a in
                                  (match uu____1259 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____1200 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____1327 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____1327 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____1336 =
                       let uu____1344 =
                         FStar_List.map
                           (fun uu____1358  ->
                              match uu____1358 with
                              | (bv,aq) ->
                                  let uu____1368 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____1368 with
                                   | (s',gs) ->
                                       (((let uu___113_1384 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___113_1384.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___113_1384.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____1344 in
                     (match uu____1336 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____1418 = traverse f pol e' topen in
                          (match uu____1418 with
                           | (topen',gs2) ->
                               let uu____1429 =
                                 let uu____1430 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____1430.FStar_Syntax_Syntax.n in
                               (uu____1429, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____1059 with
          | (tn',gs) ->
              let t' =
                let uu___114_1446 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.tk =
                    (uu___114_1446.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___114_1446.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___114_1446.FStar_Syntax_Syntax.vars)
                } in
              let uu____1451 = f pol e t' in
              (match uu____1451 with
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
      let uu____1474 = FStar_Syntax_Util.un_squash tn in
      match uu____1474 with
      | Some t' -> Some t'
      | None  ->
          let uu____1488 = FStar_Syntax_Util.head_and_args tn in
          (match uu____1488 with
           | (hd1,uu____1500) ->
               let uu____1515 =
                 let uu____1516 = FStar_Syntax_Util.un_uinst hd1 in
                 uu____1516.FStar_Syntax_Syntax.n in
               (match uu____1515 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid
                    -> Some t
                | uu____1521 -> None))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1537 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write tacdbg uu____1537);
      (let uu____1541 = FStar_ST.read tacdbg in
       if uu____1541
       then
         let uu____1544 =
           let uu____1545 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____1545
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____1546 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____1544
           uu____1546
       else ());
      (let uu____1548 = FStar_TypeChecker_Env.clear_expected_typ env in
       match uu____1548 with
       | (env1,uu____1556) ->
           let env2 =
             let uu___115_1560 = env1 in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___115_1560.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___115_1560.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___115_1560.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___115_1560.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___115_1560.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___115_1560.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___115_1560.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___115_1560.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___115_1560.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp = false;
               FStar_TypeChecker_Env.effects =
                 (uu___115_1560.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___115_1560.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___115_1560.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___115_1560.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___115_1560.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___115_1560.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___115_1560.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___115_1560.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___115_1560.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___115_1560.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.type_of =
                 (uu___115_1560.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___115_1560.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___115_1560.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___115_1560.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___115_1560.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___115_1560.FStar_TypeChecker_Env.synth)
             } in
           let initial = ((Prims.parse_int "1"), []) in
           let uu____1572 = traverse by_tactic_interp Pos env2 goal in
           (match uu____1572 with
            | (t',gs) ->
                ((let uu____1584 = FStar_ST.read tacdbg in
                  if uu____1584
                  then
                    let uu____1587 =
                      let uu____1588 = FStar_TypeChecker_Env.all_binders env2 in
                      FStar_All.pipe_right uu____1588
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu____1589 = FStar_Syntax_Print.term_to_string t' in
                    FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                      uu____1587 uu____1589
                  else ());
                 (let s = initial in
                  let s1 =
                    FStar_List.fold_left
                      (fun uu____1608  ->
                         fun g  ->
                           match uu____1608 with
                           | (n1,gs1) ->
                               let phi =
                                 let uu____1629 =
                                   getprop g.FStar_Tactics_Basic.context
                                     g.FStar_Tactics_Basic.goal_ty in
                                 match uu____1629 with
                                 | None  ->
                                     let uu____1631 =
                                       let uu____1632 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Basic.goal_ty in
                                       FStar_Util.format1
                                         "Tactic returned proof-relevant goal: %s"
                                         uu____1632 in
                                     failwith uu____1631
                                 | Some phi -> phi in
                               ((let uu____1635 =
                                   let uu____1636 =
                                     FStar_TypeChecker_Rel.teq_nosmt
                                       g.FStar_Tactics_Basic.context
                                       g.FStar_Tactics_Basic.witness
                                       FStar_Syntax_Const.exp_unit in
                                   Prims.op_Negation uu____1636 in
                                 if uu____1635
                                 then
                                   let uu____1637 =
                                     let uu____1638 =
                                       FStar_Syntax_Print.term_to_string
                                         g.FStar_Tactics_Basic.witness in
                                     FStar_Util.format1
                                       "Irrelevant tactic witness does not unify with (): %s"
                                       uu____1638 in
                                   failwith uu____1637
                                 else
                                   (let uu____1640 = FStar_ST.read tacdbg in
                                    if uu____1640
                                    then
                                      let uu____1643 =
                                        FStar_Util.string_of_int n1 in
                                      let uu____1644 =
                                        FStar_Tactics_Basic.goal_to_string g in
                                      FStar_Util.print2 "Got goal #%s: %s\n"
                                        uu____1643 uu____1644
                                    else ()));
                                (let gt' =
                                   let uu____1647 =
                                     let uu____1648 =
                                       FStar_Util.string_of_int n1 in
                                     Prims.strcat "Could not prove goal #"
                                       uu____1648 in
                                   FStar_TypeChecker_Util.label uu____1647
                                     FStar_Range.dummyRange phi in
                                 ((n1 + (Prims.parse_int "1")),
                                   (((g.FStar_Tactics_Basic.context), gt') ::
                                   gs1))))) s gs in
                  let uu____1654 = s1 in
                  match uu____1654 with
                  | (uu____1663,gs1) -> (env2, t') :: gs1))))
let reify_tactic:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun a  ->
    let r =
      let uu____1678 =
        let uu____1679 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational None in
        FStar_Syntax_Syntax.fv_to_tm uu____1679 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____1678 [FStar_Syntax_Syntax.U_zero] in
    let uu____1680 =
      let uu____1681 =
        let uu____1682 = FStar_Syntax_Syntax.iarg t_unit in
        let uu____1683 =
          let uu____1685 = FStar_Syntax_Syntax.as_arg a in [uu____1685] in
        uu____1682 :: uu____1683 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____1681 in
    uu____1680 None a.FStar_Syntax_Syntax.pos
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
          let uu____1704 = FStar_List.hd ps.FStar_Tactics_Basic.goals in
          uu____1704.FStar_Tactics_Basic.witness in
        let r =
          try
            let uu____1710 =
              let uu____1712 = reify_tactic tau in
              unembed_tactic_0 FStar_Reflection_Basic.unembed_unit uu____1712 in
            FStar_Tactics_Basic.run uu____1710 ps
          with
          | FStar_Tactics_Basic.TacFailure s ->
              FStar_Tactics_Basic.Failed ((Prims.strcat "EXCEPTION: " s), ps) in
        match r with
        | FStar_Tactics_Basic.Success (uu____1716,ps1) ->
            ((let uu____1719 = FStar_ST.read tacdbg in
              if uu____1719
              then
                let uu____1722 = FStar_Syntax_Print.term_to_string w in
                FStar_Util.print1 "Tactic generated proofterm %s\n"
                  uu____1722
              else ());
             w)
        | FStar_Tactics_Basic.Failed (s,ps1) ->
            ((let uu____1727 = FStar_Util.format1 "user tactic failed: %s" s in
              FStar_Errors.err typ.FStar_Syntax_Syntax.pos uu____1727);
             failwith "aborting")