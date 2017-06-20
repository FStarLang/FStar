open Prims
type name = FStar_Syntax_Syntax.bv
let remove_unit f x = f x ()
let quote:
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
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
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
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
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
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
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
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
         let uu____320 = let uu____321 = unembed_a (fst a) in f uu____321 in
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
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____660)::(et2,uu____662)::(embedded_state,uu____664)::[] ->
            let uu____693 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____693 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___108_702 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___108_702.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___108_702.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___108_702.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___108_702.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____705 =
                     let uu____707 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____708 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____709 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____710 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____707 uu____708
                       uu____709 uu____710 in
                   FStar_Tactics_Basic.run uu____705 ps1 in
                 let uu____711 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____711)
        | uu____712 ->
            let uu____713 =
              let uu____714 = FStar_Ident.string_of_lid nm in
              let uu____715 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____714
                uu____715 in
            failwith uu____713
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
    let uu____763 =
      mk1 "__forall_intros" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____764 =
      let uu____766 =
        mk1 "__implies_intro" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____767 =
        let uu____769 =
          mk1 "__trivial" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____770 =
          let uu____772 =
            mk1 "__revert" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____773 =
            let uu____775 =
              mk1 "__clear" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____776 =
              let uu____778 =
                mk1 "__split" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____779 =
                let uu____781 =
                  mk1 "__merge" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____782 =
                  let uu____784 =
                    mk1 "__rewrite" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____785 =
                    let uu____787 =
                      mk1 "__smt" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____788 =
                      let uu____790 =
                        mk1 "__exact" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____791 =
                        let uu____793 =
                          mk1 "__apply_lemma" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____794 =
                          let uu____796 =
                            mk1 "__visit" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____798 =
                            let uu____800 =
                              mk1 "__focus" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____802 =
                              let uu____804 =
                                mk1 "__seq" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____807 =
                                let uu____809 =
                                  mk1 "__term_as_formula"
                                    (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____811 =
                                  let uu____813 =
                                    mk1 "__inspect" (Prims.parse_int "1")
                                      (mk_pure_interpretation_1
                                         FStar_Tactics_Embedding.inspect
                                         FStar_Tactics_Embedding.unembed_term
                                         (FStar_Tactics_Embedding.embed_option
                                            FStar_Tactics_Embedding.embed_term_view
                                            FStar_Tactics_Embedding.fstar_tactics_term_view)) in
                                  let uu____815 =
                                    let uu____817 =
                                      mk1 "__pack" (Prims.parse_int "1")
                                        (mk_pure_interpretation_1
                                           FStar_Tactics_Embedding.pack
                                           FStar_Tactics_Embedding.unembed_term_view
                                           FStar_Tactics_Embedding.embed_term) in
                                    let uu____818 =
                                      let uu____820 =
                                        mk1 "__inspect_fv"
                                          (Prims.parse_int "1")
                                          (mk_pure_interpretation_1
                                             FStar_Tactics_Embedding.inspectfv
                                             FStar_Tactics_Embedding.unembed_fvar
                                             (FStar_Tactics_Embedding.embed_list
                                                FStar_Tactics_Embedding.embed_string
                                                FStar_TypeChecker_Common.t_string)) in
                                      let uu____822 =
                                        let uu____824 =
                                          mk1 "__pack_fv"
                                            (Prims.parse_int "1")
                                            (mk_pure_interpretation_1
                                               FStar_Tactics_Embedding.packfv
                                               (FStar_Tactics_Embedding.unembed_list
                                                  FStar_Tactics_Embedding.unembed_string)
                                               FStar_Tactics_Embedding.embed_fvar) in
                                        let uu____826 =
                                          let uu____828 =
                                            mk1 "__inspect_bv"
                                              (Prims.parse_int "1")
                                              (mk_pure_interpretation_1
                                                 FStar_Tactics_Embedding.inspectbv
                                                 FStar_Tactics_Embedding.unembed_binder
                                                 FStar_Tactics_Embedding.embed_string) in
                                          let uu____829 =
                                            let uu____831 =
                                              mk1 "__compare_binder"
                                                (Prims.parse_int "2")
                                                (mk_pure_interpretation_2
                                                   FStar_Tactics_Basic.order_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.embed_order) in
                                            let uu____832 =
                                              let uu____834 =
                                                mk1 "__binders_of_env"
                                                  (Prims.parse_int "1")
                                                  (binders_of_env ps) in
                                              let uu____835 =
                                                let uu____837 =
                                                  mk1 "__type_of_binder"
                                                    (Prims.parse_int "1")
                                                    type_of_binder in
                                                let uu____838 =
                                                  let uu____840 =
                                                    mk1 "__term_eq"
                                                      (Prims.parse_int "2")
                                                      term_eq in
                                                  let uu____841 =
                                                    let uu____843 =
                                                      mk1 "__print"
                                                        (Prims.parse_int "2")
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
                                                    let uu____848 =
                                                      let uu____850 =
                                                        mk1 "__dump"
                                                          (Prims.parse_int
                                                             "2")
                                                          (mk_tactic_interpretation_1
                                                             ps
                                                             FStar_Tactics_Basic.print_proof_state
                                                             FStar_Tactics_Embedding.unembed_string
                                                             FStar_Tactics_Embedding.embed_unit
                                                             FStar_TypeChecker_Common.t_unit) in
                                                      let uu____851 =
                                                        let uu____853 =
                                                          mk1
                                                            "__term_to_string"
                                                            (Prims.parse_int
                                                               "1")
                                                            (mk_pure_interpretation_1
                                                               FStar_Syntax_Print.term_to_string
                                                               FStar_Tactics_Embedding.unembed_term
                                                               FStar_Tactics_Embedding.embed_string) in
                                                        let uu____854 =
                                                          let uu____856 =
                                                            mk1 "__grewrite"
                                                              (Prims.parse_int
                                                                 "3")
                                                              (grewrite_interpretation
                                                                 ps) in
                                                          [uu____856] in
                                                        uu____853 ::
                                                          uu____854 in
                                                      uu____850 :: uu____851 in
                                                    uu____843 :: uu____848 in
                                                  uu____840 :: uu____841 in
                                                uu____837 :: uu____838 in
                                              uu____834 :: uu____835 in
                                            uu____831 :: uu____832 in
                                          uu____828 :: uu____829 in
                                        uu____824 :: uu____826 in
                                      uu____820 :: uu____822 in
                                    uu____817 :: uu____818 in
                                  uu____813 :: uu____815 in
                                uu____809 :: uu____811 in
                              uu____804 :: uu____807 in
                            uu____800 :: uu____802 in
                          uu____796 :: uu____798 in
                        uu____793 :: uu____794 in
                      uu____790 :: uu____791 in
                    uu____787 :: uu____788 in
                  uu____784 :: uu____785 in
                uu____781 :: uu____782 in
              uu____778 :: uu____779 in
            uu____775 :: uu____776 in
          uu____772 :: uu____773 in
        uu____769 :: uu____770 in
      uu____766 :: uu____767 in
    uu____763 :: uu____764
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____869 =
           let uu____870 =
             let uu____871 =
               let uu____872 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____872 in
             [uu____871] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____870 in
         uu____869 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____881 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____888  ->
              let uu____889 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____889) in
       FStar_Tactics_Basic.bind uu____881
         (fun uu____893  ->
            let result =
              let uu____895 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____895 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____897 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____904  ->
                   let uu____905 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____905) in
            FStar_Tactics_Basic.bind uu____897
              (fun uu____911  ->
                 let uu____912 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____912 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____941  ->
                          let uu____942 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____942
                            (fun uu____946  ->
                               let uu____947 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____947
                                 (fun uu____950  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____972  ->
                          let uu____973 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____973
                            (fun uu____977  ->
                               let uu____978 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____978
                                 (fun uu____981  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____997 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____997 with
            | (hd1,args) ->
                let uu____1024 =
                  let uu____1032 =
                    let uu____1033 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____1033.FStar_Syntax_Syntax.n in
                  (uu____1032, args) in
                (match uu____1024 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____1044)::(assertion,uu____1046)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____1072 =
                       let uu____1074 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___109_1078 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___109_1078.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___109_1078.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____1074
                         (fun uu____1080  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____1072
                 | uu____1081 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____1101 = FStar_Syntax_Util.head_and_args t in
      match uu____1101 with
      | (hd1,args) ->
          let uu____1130 =
            let uu____1138 =
              let uu____1139 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1139.FStar_Syntax_Syntax.n in
            (uu____1138, args) in
          (match uu____1130 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____1152)::(assertion,uu____1154)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____1180 =
                 let uu____1182 =
                   unembed_tactic_0 FStar_Tactics_Embedding.unembed_unit
                     tactic in
                 let uu____1184 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____1182 uu____1184 in
               (match uu____1180 with
                | FStar_Tactics_Basic.Success (uu____1188,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____1196 -> (t, []))
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
        let uu____1236 =
          let uu____1240 =
            let uu____1241 = FStar_Syntax_Subst.compress t in
            uu____1241.FStar_Syntax_Syntax.n in
          match uu____1240 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1253 = traverse f e t1 in
              (match uu____1253 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1271 = traverse f e t1 in
              (match uu____1271 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1284;
                 FStar_Syntax_Syntax.pos = uu____1285;
                 FStar_Syntax_Syntax.vars = uu____1286;_},(p,uu____1288)::
               (q,uu____1290)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1321 =
                let uu____1325 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1325 q in
              (match uu____1321 with
               | (q',gs) ->
                   let uu____1333 =
                     let uu____1334 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1334.FStar_Syntax_Syntax.n in
                   (uu____1333, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1354 = traverse f e hd1 in
              (match uu____1354 with
               | (hd',gs1) ->
                   let uu____1365 =
                     FStar_List.fold_right
                       (fun uu____1389  ->
                          fun uu____1390  ->
                            match (uu____1389, uu____1390) with
                            | ((a,q),(as',gs)) ->
                                let uu____1433 = traverse f e a in
                                (match uu____1433 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1365 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1501 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1501 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1510 = traverse f e' topen in
                   (match uu____1510 with
                    | (topen',gs) ->
                        let uu____1521 =
                          let uu____1522 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1522.FStar_Syntax_Syntax.n in
                        (uu____1521, gs)))
          | x -> (x, []) in
        match uu____1236 with
        | (tn',gs) ->
            let t' =
              let uu___110_1538 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___110_1538.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___110_1538.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___110_1538.FStar_Syntax_Syntax.vars)
              } in
            let uu____1543 = f e t' in
            (match uu____1543 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1568 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1568);
      (let uu____1572 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1572
       then
         let uu____1575 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1575
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1588 = traverse by_tactic_interp env goal in
       match uu____1588 with
       | (t',gs) ->
           ((let uu____1600 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1600
             then
               let uu____1603 =
                 let uu____1604 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1604
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1605 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1603 uu____1605
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1630  ->
                    fun g  ->
                      match uu____1630 with
                      | (n1,gs1) ->
                          ((let uu____1651 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1651
                            then
                              let uu____1654 = FStar_Util.string_of_int n1 in
                              let uu____1655 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1654 uu____1655
                            else ());
                           (let gt' =
                              let uu____1658 =
                                let uu____1659 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1659 in
                              FStar_TypeChecker_Util.label uu____1658
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1665 = s1 in
             match uu____1665 with | (uu____1674,gs1) -> (env, t') :: gs1)))