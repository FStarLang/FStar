open Prims
type name = FStar_Syntax_Syntax.bv
let remove_unit f x = f x ()
let quote:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | uu____33::(y,uu____35)::[] ->
          let uu____56 = FStar_Tactics_Embedding.embed_term y in
          Some uu____56
      | uu____57 -> None
let binders_of_env:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (embedded_env,uu____70)::[] ->
            let env =
              FStar_Tactics_Embedding.unembed_env
                ps.FStar_Tactics_Basic.main_context embedded_env in
            let uu____84 =
              let uu____85 = FStar_TypeChecker_Env.all_binders env in
              FStar_Tactics_Embedding.embed_binders uu____85 in
            Some uu____84
        | uu____87 -> None
let type_of_binder:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_binder,uu____97)::[] ->
          let uu____110 =
            FStar_Tactics_Embedding.unembed_binder embedded_binder in
          (match uu____110 with
           | (b,uu____113) ->
               let uu____114 =
                 FStar_Tactics_Embedding.embed_term
                   b.FStar_Syntax_Syntax.sort in
               Some uu____114)
      | uu____115 -> None
let term_eq:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun nm  ->
    fun args  ->
      match args with
      | (embedded_t1,uu____125)::(embedded_t2,uu____127)::[] ->
          let t1 = FStar_Tactics_Embedding.unembed_term embedded_t1 in
          let t2 = FStar_Tactics_Embedding.unembed_term embedded_t2 in
          let b = FStar_Syntax_Util.term_eq t1 t2 in
          let uu____151 = FStar_Tactics_Embedding.embed_bool b in
          Some uu____151
      | uu____152 -> None
let mk_pure_interpretation_2 f unembed_a unembed_b embed_c nm args =
  (let uu____216 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____216
   then
     let uu____219 = FStar_Ident.string_of_lid nm in
     let uu____220 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____219 uu____220
   else ());
  (match args with
   | (a,uu____224)::(b,uu____226)::[] ->
       let uu____247 =
         let uu____248 =
           let uu____249 = unembed_a a in
           let uu____250 = unembed_b b in f uu____249 uu____250 in
         embed_c uu____248 in
       Some uu____247
   | uu____251 -> failwith "Unexpected interpretation of pure primitive")
let mk_pure_interpretation_1 f unembed_a embed_b nm args =
  (let uu____299 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____299
   then
     let uu____302 = FStar_Ident.string_of_lid nm in
     let uu____303 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____302 uu____303
   else ());
  (match args with
   | a::[] ->
       let uu____319 =
         let uu____320 =
           let uu____321 = unembed_a (Prims.fst a) in f uu____321 in
         embed_b uu____320 in
       Some uu____319
   | uu____324 -> failwith "Unexpected interpretation of pure primitive")
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____367)::[] ->
      ((let uu____381 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____381
        then
          let uu____384 = FStar_Ident.string_of_lid nm in
          let uu____385 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.print2 "Reached %s, args are: %s\n" uu____384 uu____385
        else ());
       (let uu____387 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____387 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___105_396 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___105_396.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___105_396.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___105_396.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___105_396.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____399 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____399))
  | uu____400 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____460)::(embedded_state,uu____462)::[] ->
      ((let uu____484 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____484
        then
          let uu____487 = FStar_Ident.string_of_lid nm in
          let uu____488 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____487 uu____488
        else ());
       (let uu____490 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____490 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___106_499 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___106_499.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___106_499.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___106_499.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___106_499.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____502 = let uu____504 = unembed_b b in t uu____504 in
              FStar_Tactics_Basic.run uu____502 ps1 in
            let uu____505 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____505))
  | uu____506 ->
      let uu____507 =
        let uu____508 = FStar_Ident.string_of_lid nm in
        let uu____509 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____508 uu____509 in
      failwith uu____507
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____586)::(b,uu____588)::(embedded_state,uu____590)::[] ->
      ((let uu____620 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____620
        then
          let uu____623 = FStar_Ident.string_of_lid nm in
          let uu____624 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____623 uu____624
        else ());
       (let uu____626 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____626 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___107_635 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___107_635.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___107_635.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___107_635.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___107_635.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____638 =
                let uu____640 = unembed_a a in
                let uu____641 = unembed_b b in t uu____640 uu____641 in
              FStar_Tactics_Basic.run uu____638 ps1 in
            let uu____642 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            Some uu____642))
  | uu____643 ->
      let uu____644 =
        let uu____645 = FStar_Ident.string_of_lid nm in
        let uu____646 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____645 uu____646 in
      failwith uu____644
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____661)::(et2,uu____663)::(embedded_state,uu____665)::[] ->
            let uu____694 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____694 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___108_703 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___108_703.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___108_703.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___108_703.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___108_703.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____706 =
                     let uu____708 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____709 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____710 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____711 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____708 uu____709
                       uu____710 uu____711 in
                   FStar_Tactics_Basic.run uu____706 ps1 in
                 let uu____712 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____712)
        | uu____713 ->
            let uu____714 =
              let uu____715 = FStar_Ident.string_of_lid nm in
              let uu____716 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____715
                uu____716 in
            failwith uu____714
let step_from_native_step:
  FStar_Tactics_Basic.proofstate ->
    FStar_Tactics_Native.native_primitive_step ->
      FStar_TypeChecker_Normalize.primitive_step
  =
  fun ps  ->
    fun s  ->
      (let uu____725 = FStar_Ident.string_of_lid s.FStar_Tactics_Native.name in
       FStar_Util.print1 "Registered primitive step %s\n" uu____725);
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
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid nm in
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
    (let uu____783 =
       FStar_All.pipe_left FStar_Util.string_of_int
         (FStar_List.length native_tactics) in
     FStar_Util.print1 "Loaded %s native tactics\n" uu____783);
    (let uu____786 =
       let uu____788 =
         mk1 "__forall_intros" (Prims.parse_int "1")
           (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
              FStar_Tactics_Embedding.embed_binders
              FStar_Tactics_Embedding.fstar_tactics_binders) in
       let uu____789 =
         let uu____791 =
           mk1 "__implies_intro" (Prims.parse_int "1")
             (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
                FStar_Tactics_Embedding.embed_binder
                FStar_Tactics_Embedding.fstar_tactics_binder) in
         let uu____792 =
           let uu____794 =
             mk1 "__trivial" (Prims.parse_int "1")
               (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
                  FStar_Tactics_Embedding.embed_unit
                  FStar_TypeChecker_Common.t_unit) in
           let uu____795 =
             let uu____797 =
               mk1 "__revert" (Prims.parse_int "1")
                 (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                    FStar_Tactics_Embedding.embed_unit
                    FStar_TypeChecker_Common.t_unit) in
             let uu____798 =
               let uu____800 =
                 mk1 "__clear" (Prims.parse_int "1")
                   (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                      FStar_Tactics_Embedding.embed_unit
                      FStar_TypeChecker_Common.t_unit) in
               let uu____801 =
                 let uu____803 =
                   mk1 "__split" (Prims.parse_int "1")
                     (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                        FStar_Tactics_Embedding.embed_unit
                        FStar_TypeChecker_Common.t_unit) in
                 let uu____804 =
                   let uu____806 =
                     mk1 "__merge" (Prims.parse_int "1")
                       (mk_tactic_interpretation_0 ps
                          FStar_Tactics_Basic.merge_sub_goals
                          FStar_Tactics_Embedding.embed_unit
                          FStar_TypeChecker_Common.t_unit) in
                   let uu____807 =
                     let uu____809 =
                       mk1 "__rewrite" (Prims.parse_int "2")
                         (mk_tactic_interpretation_1 ps
                            FStar_Tactics_Basic.rewrite
                            FStar_Tactics_Embedding.unembed_binder
                            FStar_Tactics_Embedding.embed_unit
                            FStar_TypeChecker_Common.t_unit) in
                     let uu____810 =
                       let uu____812 =
                         mk1 "__smt" (Prims.parse_int "1")
                           (mk_tactic_interpretation_0 ps
                              FStar_Tactics_Basic.smt
                              FStar_Tactics_Embedding.embed_unit
                              FStar_TypeChecker_Common.t_unit) in
                       let uu____813 =
                         let uu____815 =
                           mk1 "__exact" (Prims.parse_int "2")
                             (mk_tactic_interpretation_1 ps
                                FStar_Tactics_Basic.exact
                                FStar_Tactics_Embedding.unembed_term
                                FStar_Tactics_Embedding.embed_unit
                                FStar_TypeChecker_Common.t_unit) in
                         let uu____816 =
                           let uu____818 =
                             mk1 "__apply_lemma" (Prims.parse_int "2")
                               (mk_tactic_interpretation_1 ps
                                  FStar_Tactics_Basic.apply_lemma
                                  FStar_Tactics_Embedding.unembed_term
                                  FStar_Tactics_Embedding.embed_unit
                                  FStar_TypeChecker_Common.t_unit) in
                           let uu____819 =
                             let uu____821 =
                               mk1 "__visit" (Prims.parse_int "2")
                                 (mk_tactic_interpretation_1 ps
                                    FStar_Tactics_Basic.visit
                                    (unembed_tactic_0
                                       FStar_Tactics_Embedding.unembed_unit)
                                    FStar_Tactics_Embedding.embed_unit
                                    FStar_TypeChecker_Common.t_unit) in
                             let uu____823 =
                               let uu____825 =
                                 mk1 "__focus" (Prims.parse_int "2")
                                   (mk_tactic_interpretation_1 ps
                                      (FStar_Tactics_Basic.focus_cur_goal
                                         "user_tactic")
                                      (unembed_tactic_0
                                         FStar_Tactics_Embedding.unembed_unit)
                                      FStar_Tactics_Embedding.embed_unit
                                      FStar_TypeChecker_Common.t_unit) in
                               let uu____827 =
                                 let uu____829 =
                                   mk1 "__seq" (Prims.parse_int "3")
                                     (mk_tactic_interpretation_2 ps
                                        FStar_Tactics_Basic.seq
                                        (unembed_tactic_0
                                           FStar_Tactics_Embedding.unembed_unit)
                                        (unembed_tactic_0
                                           FStar_Tactics_Embedding.unembed_unit)
                                        FStar_Tactics_Embedding.embed_unit
                                        FStar_TypeChecker_Common.t_unit) in
                                 let uu____832 =
                                   let uu____834 =
                                     mk1 "__term_as_formula"
                                       (Prims.parse_int "1")
                                       (mk_pure_interpretation_1
                                          FStar_Tactics_Embedding.term_as_formula
                                          FStar_Tactics_Embedding.unembed_term
                                          (FStar_Tactics_Embedding.embed_option
                                             FStar_Tactics_Embedding.embed_formula
                                             FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                   let uu____836 =
                                     let uu____838 =
                                       mk1 "__inspect" (Prims.parse_int "1")
                                         (mk_pure_interpretation_1
                                            FStar_Tactics_Embedding.inspect
                                            FStar_Tactics_Embedding.unembed_term
                                            (FStar_Tactics_Embedding.embed_option
                                               FStar_Tactics_Embedding.embed_term_view
                                               FStar_Tactics_Embedding.fstar_tactics_term_view)) in
                                     let uu____840 =
                                       let uu____842 =
                                         mk1 "__pack" (Prims.parse_int "1")
                                           (mk_pure_interpretation_1
                                              FStar_Tactics_Embedding.pack
                                              FStar_Tactics_Embedding.unembed_term_view
                                              FStar_Tactics_Embedding.embed_term) in
                                       let uu____843 =
                                         let uu____845 =
                                           mk1 "__inspect_fv"
                                             (Prims.parse_int "1")
                                             (mk_pure_interpretation_1
                                                FStar_Tactics_Embedding.inspectfv
                                                FStar_Tactics_Embedding.unembed_fvar
                                                (FStar_Tactics_Embedding.embed_list
                                                   FStar_Tactics_Embedding.embed_string
                                                   FStar_TypeChecker_Common.t_string)) in
                                         let uu____847 =
                                           let uu____849 =
                                             mk1 "__pack_fv"
                                               (Prims.parse_int "1")
                                               (mk_pure_interpretation_1
                                                  FStar_Tactics_Embedding.packfv
                                                  (FStar_Tactics_Embedding.unembed_list
                                                     FStar_Tactics_Embedding.unembed_string)
                                                  FStar_Tactics_Embedding.embed_fvar) in
                                           let uu____851 =
                                             let uu____853 =
                                               mk1 "__inspect_bv"
                                                 (Prims.parse_int "1")
                                                 (mk_pure_interpretation_1
                                                    FStar_Tactics_Embedding.inspectbv
                                                    FStar_Tactics_Embedding.unembed_binder
                                                    FStar_Tactics_Embedding.embed_string) in
                                             let uu____854 =
                                               let uu____856 =
                                                 mk1 "__compare_binder"
                                                   (Prims.parse_int "2")
                                                   (mk_pure_interpretation_2
                                                      FStar_Tactics_Basic.order_binder
                                                      FStar_Tactics_Embedding.unembed_binder
                                                      FStar_Tactics_Embedding.unembed_binder
                                                      FStar_Tactics_Embedding.embed_order) in
                                               let uu____857 =
                                                 let uu____859 =
                                                   mk1 "__binders_of_env"
                                                     (Prims.parse_int "1")
                                                     (binders_of_env ps) in
                                                 let uu____860 =
                                                   let uu____862 =
                                                     mk1 "__type_of_binder"
                                                       (Prims.parse_int "1")
                                                       type_of_binder in
                                                   let uu____863 =
                                                     let uu____865 =
                                                       mk1 "__term_eq"
                                                         (Prims.parse_int "2")
                                                         term_eq in
                                                     let uu____866 =
                                                       let uu____868 =
                                                         mk1 "__print"
                                                           (Prims.parse_int
                                                              "2")
                                                           (mk_tactic_interpretation_1
                                                              ps
                                                              (fun x  ->
                                                                 FStar_Tactics_Basic.tacprint
                                                                   x;
                                                                 FStar_Tactics_Basic.ret
                                                                   ())
                                                              FStar_Tactics_Embedding.unembed_string
                                                              FStar_Tactics_Embedding.embed_unit
                                                              FStar_TypeChecker_Common.t_unit) in
                                                       let uu____871 =
                                                         let uu____873 =
                                                           mk1 "__dump"
                                                             (Prims.parse_int
                                                                "2")
                                                             (mk_tactic_interpretation_1
                                                                ps
                                                                FStar_Tactics_Basic.print_proof_state
                                                                FStar_Tactics_Embedding.unembed_string
                                                                FStar_Tactics_Embedding.embed_unit
                                                                FStar_TypeChecker_Common.t_unit) in
                                                         let uu____874 =
                                                           let uu____876 =
                                                             mk1
                                                               "__term_to_string"
                                                               (Prims.parse_int
                                                                  "1")
                                                               (mk_pure_interpretation_1
                                                                  FStar_Syntax_Print.term_to_string
                                                                  FStar_Tactics_Embedding.unembed_term
                                                                  FStar_Tactics_Embedding.embed_string) in
                                                           let uu____877 =
                                                             let uu____879 =
                                                               mk1
                                                                 "__grewrite"
                                                                 (Prims.parse_int
                                                                    "3")
                                                                 (grewrite_interpretation
                                                                    ps) in
                                                             [uu____879] in
                                                           uu____876 ::
                                                             uu____877 in
                                                         uu____873 ::
                                                           uu____874 in
                                                       uu____868 :: uu____871 in
                                                     uu____865 :: uu____866 in
                                                   uu____862 :: uu____863 in
                                                 uu____859 :: uu____860 in
                                               uu____856 :: uu____857 in
                                             uu____853 :: uu____854 in
                                           uu____849 :: uu____851 in
                                         uu____845 :: uu____847 in
                                       uu____842 :: uu____843 in
                                     uu____838 :: uu____840 in
                                   uu____834 :: uu____836 in
                                 uu____829 :: uu____832 in
                               uu____825 :: uu____827 in
                             uu____821 :: uu____823 in
                           uu____818 :: uu____819 in
                         uu____815 :: uu____816 in
                       uu____812 :: uu____813 in
                     uu____809 :: uu____810 in
                   uu____806 :: uu____807 in
                 uu____803 :: uu____804 in
               uu____800 :: uu____801 in
             uu____797 :: uu____798 in
           uu____794 :: uu____795 in
         uu____791 :: uu____792 in
       uu____788 :: uu____789 in
     FStar_List.append uu____786 native_tactics_steps)
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____888 =
           let uu____889 =
             let uu____890 =
               let uu____891 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____891 in
             [uu____890] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____889 in
         uu____888 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____900 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____905  ->
              let uu____906 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____906) in
       FStar_Tactics_Basic.bind uu____900
         (fun uu____907  ->
            let result =
              let uu____909 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____909 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____911 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____916  ->
                   let uu____917 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____917) in
            FStar_Tactics_Basic.bind uu____911
              (fun uu____918  ->
                 let uu____919 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____919 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____946  ->
                          let uu____947 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____947
                            (fun uu____949  ->
                               let uu____950 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____950
                                 (fun uu____952  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____972  ->
                          let uu____973 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____973
                            (fun uu____975  ->
                               let uu____976 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____976
                                 (fun uu____978  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____982 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____982 with
            | (hd1,args) ->
                let uu____1009 =
                  let uu____1017 =
                    let uu____1018 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____1018.FStar_Syntax_Syntax.n in
                  (uu____1017, args) in
                (match uu____1009 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____1029)::(assertion,uu____1031)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____1057 =
                       let uu____1059 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___109_1061 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___109_1061.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___109_1061.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____1059
                         (fun uu____1062  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____1057
                 | uu____1063 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____1083 = FStar_Syntax_Util.head_and_args t in
      match uu____1083 with
      | (hd1,args) ->
          let uu____1112 =
            let uu____1120 =
              let uu____1121 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1121.FStar_Syntax_Syntax.n in
            (uu____1120, args) in
          (match uu____1112 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____1134)::(assertion,uu____1136)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____1162 =
                 let uu____1164 =
                   unembed_tactic_0 FStar_Tactics_Embedding.unembed_unit
                     tactic in
                 let uu____1166 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____1164 uu____1166 in
               (match uu____1162 with
                | FStar_Tactics_Basic.Success (uu____1170,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____1178 -> (t, []))
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
        let uu____1218 =
          let uu____1222 =
            let uu____1223 = FStar_Syntax_Subst.compress t in
            uu____1223.FStar_Syntax_Syntax.n in
          match uu____1222 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1235 = traverse f e t1 in
              (match uu____1235 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1253 = traverse f e t1 in
              (match uu____1253 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1266;
                 FStar_Syntax_Syntax.pos = uu____1267;
                 FStar_Syntax_Syntax.vars = uu____1268;_},(p,uu____1270)::
               (q,uu____1272)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1303 =
                let uu____1307 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1307 q in
              (match uu____1303 with
               | (q',gs) ->
                   let uu____1315 =
                     let uu____1316 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1316.FStar_Syntax_Syntax.n in
                   (uu____1315, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1336 = traverse f e hd1 in
              (match uu____1336 with
               | (hd',gs1) ->
                   let uu____1347 =
                     FStar_List.fold_right
                       (fun uu____1362  ->
                          fun uu____1363  ->
                            match (uu____1362, uu____1363) with
                            | ((a,q),(as',gs)) ->
                                let uu____1406 = traverse f e a in
                                (match uu____1406 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1347 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1474 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1474 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1483 = traverse f e' topen in
                   (match uu____1483 with
                    | (topen',gs) ->
                        let uu____1494 =
                          let uu____1495 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1495.FStar_Syntax_Syntax.n in
                        (uu____1494, gs)))
          | x -> (x, []) in
        match uu____1218 with
        | (tn',gs) ->
            let t' =
              let uu___110_1511 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___110_1511.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___110_1511.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___110_1511.FStar_Syntax_Syntax.vars)
              } in
            let uu____1516 = f e t' in
            (match uu____1516 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1541 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1541);
      (let uu____1545 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1545
       then
         let uu____1548 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1548
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1561 = traverse by_tactic_interp env goal in
       match uu____1561 with
       | (t',gs) ->
           ((let uu____1573 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1573
             then
               let uu____1576 =
                 let uu____1577 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1577
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1578 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1576 uu____1578
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1597  ->
                    fun g  ->
                      match uu____1597 with
                      | (n1,gs1) ->
                          ((let uu____1618 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1618
                            then
                              let uu____1621 = FStar_Util.string_of_int n1 in
                              let uu____1622 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1621 uu____1622
                            else ());
                           (let gt' =
                              let uu____1625 =
                                let uu____1626 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1626 in
                              FStar_TypeChecker_Util.label uu____1625
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1632 = s1 in
             match uu____1632 with | (uu____1641,gs1) -> (env, t') :: gs1)))