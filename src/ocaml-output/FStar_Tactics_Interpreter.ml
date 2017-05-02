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
          let uu____150 = FStar_Syntax_Util.eq_tm t1 t2 in
          (match uu____150 with
           | FStar_Syntax_Util.Equal  ->
               let uu____152 = FStar_Tactics_Embedding.embed_bool true in
               Some uu____152
           | uu____153 ->
               let uu____154 = FStar_Tactics_Embedding.embed_bool false in
               Some uu____154)
      | uu____155 -> None
let mk_pure_interpretation_2 f unembed_a unembed_b embed_c nm args =
  (let uu____219 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____219
   then
     let uu____222 = FStar_Ident.string_of_lid nm in
     let uu____223 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____222 uu____223
   else ());
  (match args with
   | (a,uu____227)::(b,uu____229)::[] ->
       let uu____250 =
         let uu____251 =
           let uu____252 = unembed_a a in
           let uu____253 = unembed_b b in f uu____252 uu____253 in
         embed_c uu____251 in
       Some uu____250
   | uu____254 -> failwith "Unexpected interpretation of pure primitive")
let mk_pure_interpretation_1 f unembed_a embed_b nm args =
  (let uu____302 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
   if uu____302
   then
     let uu____305 = FStar_Ident.string_of_lid nm in
     let uu____306 = FStar_Syntax_Print.args_to_string args in
     FStar_Util.print2 "Reached %s, args are: %s\n" uu____305 uu____306
   else ());
  (match args with
   | a::[] ->
       let uu____322 =
         let uu____323 =
           let uu____324 = unembed_a (Prims.fst a) in f uu____324 in
         embed_b uu____323 in
       Some uu____322
   | uu____327 -> failwith "Unexpected interpretation of pure primitive")
let mk_tactic_interpretation_0 ps t embed_a t_a nm args =
  match args with
  | (embedded_state,uu____370)::[] ->
      ((let uu____384 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____384
        then
          let uu____387 = FStar_Ident.string_of_lid nm in
          let uu____388 = FStar_Syntax_Print.args_to_string args in
          FStar_Util.print2 "Reached %s, args are: %s\n" uu____387 uu____388
        else ());
       (let uu____390 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____390 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___108_399 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___108_399.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___108_399.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___108_399.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___108_399.FStar_Tactics_Basic.transaction)
              } in
            let res = FStar_Tactics_Basic.run t ps1 in
            let uu____402 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____402))
  | uu____403 -> failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1 ps t unembed_b embed_a t_a nm args =
  match args with
  | (b,uu____463)::(embedded_state,uu____465)::[] ->
      ((let uu____487 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____487
        then
          let uu____490 = FStar_Ident.string_of_lid nm in
          let uu____491 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____490 uu____491
        else ());
       (let uu____493 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____493 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___109_502 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___109_502.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___109_502.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___109_502.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___109_502.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____505 = let uu____507 = unembed_b b in t uu____507 in
              FStar_Tactics_Basic.run uu____505 ps1 in
            let uu____508 =
              FStar_Tactics_Embedding.embed_result res embed_a t_a in
            Some uu____508))
  | uu____509 ->
      let uu____510 =
        let uu____511 = FStar_Ident.string_of_lid nm in
        let uu____512 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____511 uu____512 in
      failwith uu____510
let mk_tactic_interpretation_2 ps t unembed_a unembed_b embed_c t_c nm args =
  match args with
  | (a,uu____589)::(b,uu____591)::(embedded_state,uu____593)::[] ->
      ((let uu____623 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
        if uu____623
        then
          let uu____626 = FStar_Ident.string_of_lid nm in
          let uu____627 = FStar_Syntax_Print.term_to_string embedded_state in
          FStar_Util.print2 "Reached %s, goals are: %s\n" uu____626 uu____627
        else ());
       (let uu____629 =
          FStar_Tactics_Embedding.unembed_state
            ps.FStar_Tactics_Basic.main_context embedded_state in
        match uu____629 with
        | (goals,smt_goals) ->
            let ps1 =
              let uu___110_638 = ps in
              {
                FStar_Tactics_Basic.main_context =
                  (uu___110_638.FStar_Tactics_Basic.main_context);
                FStar_Tactics_Basic.main_goal =
                  (uu___110_638.FStar_Tactics_Basic.main_goal);
                FStar_Tactics_Basic.all_implicits =
                  (uu___110_638.FStar_Tactics_Basic.all_implicits);
                FStar_Tactics_Basic.goals = goals;
                FStar_Tactics_Basic.smt_goals = smt_goals;
                FStar_Tactics_Basic.transaction =
                  (uu___110_638.FStar_Tactics_Basic.transaction)
              } in
            let res =
              let uu____641 =
                let uu____643 = unembed_a a in
                let uu____644 = unembed_b b in t uu____643 uu____644 in
              FStar_Tactics_Basic.run uu____641 ps1 in
            let uu____645 =
              FStar_Tactics_Embedding.embed_result res embed_c t_c in
            Some uu____645))
  | uu____646 ->
      let uu____647 =
        let uu____648 = FStar_Ident.string_of_lid nm in
        let uu____649 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "Unexpected application of tactic primitive %s %s"
          uu____648 uu____649 in
      failwith uu____647
let grewrite_interpretation:
  FStar_Tactics_Basic.proofstate ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term Prims.option
  =
  fun ps  ->
    fun nm  ->
      fun args  ->
        match args with
        | (et1,uu____664)::(et2,uu____666)::(embedded_state,uu____668)::[] ->
            let uu____697 =
              FStar_Tactics_Embedding.unembed_state
                ps.FStar_Tactics_Basic.main_context embedded_state in
            (match uu____697 with
             | (goals,smt_goals) ->
                 let ps1 =
                   let uu___111_706 = ps in
                   {
                     FStar_Tactics_Basic.main_context =
                       (uu___111_706.FStar_Tactics_Basic.main_context);
                     FStar_Tactics_Basic.main_goal =
                       (uu___111_706.FStar_Tactics_Basic.main_goal);
                     FStar_Tactics_Basic.all_implicits =
                       (uu___111_706.FStar_Tactics_Basic.all_implicits);
                     FStar_Tactics_Basic.goals = goals;
                     FStar_Tactics_Basic.smt_goals = smt_goals;
                     FStar_Tactics_Basic.transaction =
                       (uu___111_706.FStar_Tactics_Basic.transaction)
                   } in
                 let res =
                   let uu____709 =
                     let uu____711 =
                       FStar_Tactics_Embedding.type_of_embedded et1 in
                     let uu____712 =
                       FStar_Tactics_Embedding.type_of_embedded et2 in
                     let uu____713 = FStar_Tactics_Embedding.unembed_term et1 in
                     let uu____714 = FStar_Tactics_Embedding.unembed_term et2 in
                     FStar_Tactics_Basic.grewrite_impl uu____711 uu____712
                       uu____713 uu____714 in
                   FStar_Tactics_Basic.run uu____709 ps1 in
                 let uu____715 =
                   FStar_Tactics_Embedding.embed_result res
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit in
                 Some uu____715)
        | uu____716 ->
            let uu____717 =
              let uu____718 = FStar_Ident.string_of_lid nm in
              let uu____719 = FStar_Syntax_Print.args_to_string args in
              FStar_Util.format2
                "Unexpected application of tactic primitive %s %s" uu____718
                uu____719 in
            failwith uu____717
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
    let uu____765 =
      mk1 "__forall_intros" (Prims.parse_int "1")
        (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.intros
           FStar_Tactics_Embedding.embed_binders
           FStar_Tactics_Embedding.fstar_tactics_binders) in
    let uu____766 =
      let uu____768 =
        mk1 "__implies_intro" (Prims.parse_int "1")
          (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.imp_intro
             FStar_Tactics_Embedding.embed_binder
             FStar_Tactics_Embedding.fstar_tactics_binder) in
      let uu____769 =
        let uu____771 =
          mk1 "__trivial" (Prims.parse_int "1")
            (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.trivial
               FStar_Tactics_Embedding.embed_unit
               FStar_TypeChecker_Common.t_unit) in
        let uu____772 =
          let uu____774 =
            mk1 "__revert" (Prims.parse_int "1")
              (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.revert
                 FStar_Tactics_Embedding.embed_unit
                 FStar_TypeChecker_Common.t_unit) in
          let uu____775 =
            let uu____777 =
              mk1 "__clear" (Prims.parse_int "1")
                (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.clear
                   FStar_Tactics_Embedding.embed_unit
                   FStar_TypeChecker_Common.t_unit) in
            let uu____778 =
              let uu____780 =
                mk1 "__split" (Prims.parse_int "1")
                  (mk_tactic_interpretation_0 ps FStar_Tactics_Basic.split
                     FStar_Tactics_Embedding.embed_unit
                     FStar_TypeChecker_Common.t_unit) in
              let uu____781 =
                let uu____783 =
                  mk1 "__merge" (Prims.parse_int "1")
                    (mk_tactic_interpretation_0 ps
                       FStar_Tactics_Basic.merge_sub_goals
                       FStar_Tactics_Embedding.embed_unit
                       FStar_TypeChecker_Common.t_unit) in
                let uu____784 =
                  let uu____786 =
                    mk1 "__rewrite" (Prims.parse_int "2")
                      (mk_tactic_interpretation_1 ps
                         FStar_Tactics_Basic.rewrite
                         FStar_Tactics_Embedding.unembed_binder
                         FStar_Tactics_Embedding.embed_unit
                         FStar_TypeChecker_Common.t_unit) in
                  let uu____787 =
                    let uu____789 =
                      mk1 "__smt" (Prims.parse_int "1")
                        (mk_tactic_interpretation_0 ps
                           FStar_Tactics_Basic.smt
                           FStar_Tactics_Embedding.embed_unit
                           FStar_TypeChecker_Common.t_unit) in
                    let uu____790 =
                      let uu____792 =
                        mk1 "__exact" (Prims.parse_int "2")
                          (mk_tactic_interpretation_1 ps
                             FStar_Tactics_Basic.exact
                             FStar_Tactics_Embedding.unembed_term
                             FStar_Tactics_Embedding.embed_unit
                             FStar_TypeChecker_Common.t_unit) in
                      let uu____793 =
                        let uu____795 =
                          mk1 "__apply_lemma" (Prims.parse_int "2")
                            (mk_tactic_interpretation_1 ps
                               FStar_Tactics_Basic.apply_lemma
                               FStar_Tactics_Embedding.unembed_term
                               FStar_Tactics_Embedding.embed_unit
                               FStar_TypeChecker_Common.t_unit) in
                        let uu____796 =
                          let uu____798 =
                            mk1 "__visit" (Prims.parse_int "2")
                              (mk_tactic_interpretation_1 ps
                                 FStar_Tactics_Basic.visit
                                 (unembed_tactic_0
                                    FStar_Tactics_Embedding.unembed_unit)
                                 FStar_Tactics_Embedding.embed_unit
                                 FStar_TypeChecker_Common.t_unit) in
                          let uu____800 =
                            let uu____802 =
                              mk1 "__focus" (Prims.parse_int "2")
                                (mk_tactic_interpretation_1 ps
                                   (FStar_Tactics_Basic.focus_cur_goal
                                      "user_tactic")
                                   (unembed_tactic_0
                                      FStar_Tactics_Embedding.unembed_unit)
                                   FStar_Tactics_Embedding.embed_unit
                                   FStar_TypeChecker_Common.t_unit) in
                            let uu____804 =
                              let uu____806 =
                                mk1 "__seq" (Prims.parse_int "3")
                                  (mk_tactic_interpretation_2 ps
                                     FStar_Tactics_Basic.seq
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     (unembed_tactic_0
                                        FStar_Tactics_Embedding.unembed_unit)
                                     FStar_Tactics_Embedding.embed_unit
                                     FStar_TypeChecker_Common.t_unit) in
                              let uu____809 =
                                let uu____811 =
                                  mk1 "__term_as_formula"
                                    (Prims.parse_int "1")
                                    (mk_pure_interpretation_1
                                       FStar_Tactics_Embedding.term_as_formula
                                       FStar_Tactics_Embedding.unembed_term
                                       (FStar_Tactics_Embedding.embed_option
                                          FStar_Tactics_Embedding.embed_formula
                                          FStar_Tactics_Embedding.fstar_tactics_formula)) in
                                let uu____813 =
                                  let uu____815 =
                                    mk1 "__inspect" (Prims.parse_int "1")
                                      (mk_pure_interpretation_1
                                         FStar_Tactics_Embedding.inspect
                                         FStar_Tactics_Embedding.unembed_term
                                         (FStar_Tactics_Embedding.embed_option
                                            FStar_Tactics_Embedding.embed_term_view
                                            FStar_Tactics_Embedding.fstar_tactics_term_view)) in
                                  let uu____817 =
                                    let uu____819 =
                                      mk1 "__pack" (Prims.parse_int "1")
                                        (mk_pure_interpretation_1
                                           FStar_Tactics_Embedding.pack
                                           FStar_Tactics_Embedding.unembed_term_view
                                           FStar_Tactics_Embedding.embed_term) in
                                    let uu____820 =
                                      let uu____822 =
                                        mk1 "__inspect_fv"
                                          (Prims.parse_int "1")
                                          (mk_pure_interpretation_1
                                             FStar_Tactics_Embedding.inspectfv
                                             FStar_Tactics_Embedding.unembed_fvar
                                             (FStar_Tactics_Embedding.embed_list
                                                FStar_Tactics_Embedding.embed_string
                                                FStar_TypeChecker_Common.t_string)) in
                                      let uu____824 =
                                        let uu____826 =
                                          mk1 "__pack_fv"
                                            (Prims.parse_int "1")
                                            (mk_pure_interpretation_1
                                               FStar_Tactics_Embedding.packfv
                                               (FStar_Tactics_Embedding.unembed_list
                                                  FStar_Tactics_Embedding.unembed_string)
                                               FStar_Tactics_Embedding.embed_fvar) in
                                        let uu____828 =
                                          let uu____830 =
                                            mk1 "__inspect_bv"
                                              (Prims.parse_int "1")
                                              (mk_pure_interpretation_1
                                                 FStar_Tactics_Embedding.inspectbv
                                                 FStar_Tactics_Embedding.unembed_binder
                                                 FStar_Tactics_Embedding.embed_string) in
                                          let uu____831 =
                                            let uu____833 =
                                              mk1 "__compare_binder"
                                                (Prims.parse_int "2")
                                                (mk_pure_interpretation_2
                                                   FStar_Tactics_Basic.order_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.unembed_binder
                                                   FStar_Tactics_Embedding.embed_order) in
                                            let uu____834 =
                                              let uu____836 =
                                                mk1 "__binders_of_env"
                                                  (Prims.parse_int "1")
                                                  (binders_of_env ps) in
                                              let uu____837 =
                                                let uu____839 =
                                                  mk1 "__type_of_binder"
                                                    (Prims.parse_int "1")
                                                    type_of_binder in
                                                let uu____840 =
                                                  let uu____842 =
                                                    mk1 "__term_eq"
                                                      (Prims.parse_int "2")
                                                      term_eq in
                                                  let uu____843 =
                                                    let uu____845 =
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
                                                    uu____845 :: uu____848 in
                                                  uu____842 :: uu____843 in
                                                uu____839 :: uu____840 in
                                              uu____836 :: uu____837 in
                                            uu____833 :: uu____834 in
                                          uu____830 :: uu____831 in
                                        uu____826 :: uu____828 in
                                      uu____822 :: uu____824 in
                                    uu____819 :: uu____820 in
                                  uu____815 :: uu____817 in
                                uu____811 :: uu____813 in
                              uu____806 :: uu____809 in
                            uu____802 :: uu____804 in
                          uu____798 :: uu____800 in
                        uu____795 :: uu____796 in
                      uu____792 :: uu____793 in
                    uu____789 :: uu____790 in
                  uu____786 :: uu____787 in
                uu____783 :: uu____784 in
              uu____780 :: uu____781 in
            uu____777 :: uu____778 in
          uu____774 :: uu____775 in
        uu____771 :: uu____772 in
      uu____768 :: uu____769 in
    uu____765 :: uu____766
and unembed_tactic_0 unembed_b embedded_tac_b =
  FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
    (fun proof_state  ->
       let tm =
         let uu____865 =
           let uu____866 =
             let uu____867 =
               let uu____868 =
                 FStar_Tactics_Embedding.embed_state
                   ((proof_state.FStar_Tactics_Basic.goals), []) in
               FStar_Syntax_Syntax.as_arg uu____868 in
             [uu____867] in
           FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____866 in
         uu____865 None FStar_Range.dummyRange in
       let steps =
         [FStar_TypeChecker_Normalize.Reify;
         FStar_TypeChecker_Normalize.Beta;
         FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant;
         FStar_TypeChecker_Normalize.Zeta;
         FStar_TypeChecker_Normalize.Iota;
         FStar_TypeChecker_Normalize.Primops] in
       let uu____877 =
         FStar_All.pipe_left FStar_Tactics_Basic.mlog
           (fun uu____882  ->
              let uu____883 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____883) in
       FStar_Tactics_Basic.bind uu____877
         (fun uu____884  ->
            let result =
              let uu____886 = primitive_steps proof_state in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____886 steps proof_state.FStar_Tactics_Basic.main_context
                tm in
            let uu____888 =
              FStar_All.pipe_left FStar_Tactics_Basic.mlog
                (fun uu____893  ->
                   let uu____894 = FStar_Syntax_Print.term_to_string result in
                   FStar_Util.print1 "Reduced tactic: got %s\n" uu____894) in
            FStar_Tactics_Basic.bind uu____888
              (fun uu____895  ->
                 let uu____896 =
                   FStar_Tactics_Embedding.unembed_result
                     proof_state.FStar_Tactics_Basic.main_context result
                     unembed_b in
                 match uu____896 with
                 | FStar_Util.Inl (b,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____923  ->
                          let uu____924 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____924
                            (fun uu____926  ->
                               let uu____927 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____927
                                 (fun uu____929  -> FStar_Tactics_Basic.ret b)))
                 | FStar_Util.Inr (msg,(goals,smt_goals)) ->
                     FStar_Tactics_Basic.bind FStar_Tactics_Basic.dismiss
                       (fun uu____949  ->
                          let uu____950 = FStar_Tactics_Basic.add_goals goals in
                          FStar_Tactics_Basic.bind uu____950
                            (fun uu____952  ->
                               let uu____953 =
                                 FStar_Tactics_Basic.add_smt_goals smt_goals in
                               FStar_Tactics_Basic.bind uu____953
                                 (fun uu____955  ->
                                    FStar_Tactics_Basic.fail msg))))))
let evaluate_user_tactic: Prims.unit FStar_Tactics_Basic.tac =
  FStar_Tactics_Basic.with_cur_goal "evaluate_user_tactic"
    (fun goal  ->
       FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
         (fun proof_state  ->
            let uu____959 =
              FStar_Syntax_Util.head_and_args
                goal.FStar_Tactics_Basic.goal_ty in
            match uu____959 with
            | (hd1,args) ->
                let uu____986 =
                  let uu____994 =
                    let uu____995 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____995.FStar_Syntax_Syntax.n in
                  (uu____994, args) in
                (match uu____986 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(tactic,uu____1006)::(assertion,uu____1008)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Tactics_Embedding.by_tactic_lid
                     ->
                     let uu____1034 =
                       let uu____1036 =
                         FStar_Tactics_Basic.replace_cur
                           (let uu___112_1038 = goal in
                            {
                              FStar_Tactics_Basic.context =
                                (uu___112_1038.FStar_Tactics_Basic.context);
                              FStar_Tactics_Basic.witness =
                                (uu___112_1038.FStar_Tactics_Basic.witness);
                              FStar_Tactics_Basic.goal_ty = assertion
                            }) in
                       FStar_Tactics_Basic.bind uu____1036
                         (fun uu____1039  ->
                            unembed_tactic_0
                              FStar_Tactics_Embedding.unembed_unit tactic) in
                     FStar_Tactics_Basic.focus_cur_goal "user tactic"
                       uu____1034
                 | uu____1040 -> FStar_Tactics_Basic.fail "Not a user tactic")))
let by_tactic_interp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term* FStar_Tactics_Basic.goal Prims.list)
  =
  fun e  ->
    fun t  ->
      let uu____1060 = FStar_Syntax_Util.head_and_args t in
      match uu____1060 with
      | (hd1,args) ->
          let uu____1089 =
            let uu____1097 =
              let uu____1098 = FStar_Syntax_Util.un_uinst hd1 in
              uu____1098.FStar_Syntax_Syntax.n in
            (uu____1097, args) in
          (match uu____1089 with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,(tactic,uu____1111)::(assertion,uu____1113)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Tactics_Embedding.by_tactic_lid
               ->
               let uu____1139 =
                 let uu____1141 =
                   unembed_tactic_0 FStar_Tactics_Embedding.unembed_unit
                     tactic in
                 let uu____1143 =
                   FStar_Tactics_Basic.proofstate_of_goal_ty e assertion in
                 FStar_Tactics_Basic.run uu____1141 uu____1143 in
               (match uu____1139 with
                | FStar_Tactics_Basic.Success (uu____1147,ps) ->
                    (FStar_Syntax_Util.t_true,
                      (FStar_List.append ps.FStar_Tactics_Basic.goals
                         ps.FStar_Tactics_Basic.smt_goals))
                | FStar_Tactics_Basic.Failed (s,ps) ->
                    Prims.raise
                      (FStar_Errors.Error
                         ((Prims.strcat "user tactic failed: \""
                             (Prims.strcat s "\"")),
                           (tactic.FStar_Syntax_Syntax.pos))))
           | uu____1155 -> (t, []))
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
        let uu____1195 =
          let uu____1199 =
            let uu____1200 = FStar_Syntax_Subst.compress t in
            uu____1200.FStar_Syntax_Syntax.n in
          match uu____1199 with
          | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
              let uu____1212 = traverse f e t1 in
              (match uu____1212 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
          | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
              let uu____1230 = traverse f e t1 in
              (match uu____1230 with
               | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
          | FStar_Syntax_Syntax.Tm_app
              ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                 FStar_Syntax_Syntax.tk = uu____1243;
                 FStar_Syntax_Syntax.pos = uu____1244;
                 FStar_Syntax_Syntax.vars = uu____1245;_},(p,uu____1247)::
               (q,uu____1249)::[])
              when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid ->
              let x = FStar_Syntax_Syntax.new_bv None p in
              let uu____1280 =
                let uu____1284 = FStar_TypeChecker_Env.push_bv e x in
                traverse f uu____1284 q in
              (match uu____1280 with
               | (q',gs) ->
                   let uu____1292 =
                     let uu____1293 = FStar_Syntax_Util.mk_imp p q' in
                     uu____1293.FStar_Syntax_Syntax.n in
                   (uu____1292, gs))
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let uu____1313 = traverse f e hd1 in
              (match uu____1313 with
               | (hd',gs1) ->
                   let uu____1324 =
                     FStar_List.fold_right
                       (fun uu____1339  ->
                          fun uu____1340  ->
                            match (uu____1339, uu____1340) with
                            | ((a,q),(as',gs)) ->
                                let uu____1383 = traverse f e a in
                                (match uu____1383 with
                                 | (a',gs') ->
                                     (((a', q) :: as'),
                                       (FStar_List.append gs gs')))) args
                       ([], []) in
                   (match uu____1324 with
                    | (as',gs2) ->
                        ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                          (FStar_List.append gs1 gs2))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____1451 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____1451 with
               | (bs1,topen) ->
                   let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                   let uu____1460 = traverse f e' topen in
                   (match uu____1460 with
                    | (topen',gs) ->
                        let uu____1471 =
                          let uu____1472 = FStar_Syntax_Util.abs bs1 topen' k in
                          uu____1472.FStar_Syntax_Syntax.n in
                        (uu____1471, gs)))
          | x -> (x, []) in
        match uu____1195 with
        | (tn',gs) ->
            let t' =
              let uu___113_1488 = t in
              {
                FStar_Syntax_Syntax.n = tn';
                FStar_Syntax_Syntax.tk =
                  (uu___113_1488.FStar_Syntax_Syntax.tk);
                FStar_Syntax_Syntax.pos =
                  (uu___113_1488.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars =
                  (uu___113_1488.FStar_Syntax_Syntax.vars)
              } in
            let uu____1493 = f e t' in
            (match uu____1493 with
             | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env* FStar_Syntax_Syntax.term) Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____1518 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.write FStar_Tactics_Basic.tacdbg uu____1518);
      (let uu____1522 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
       if uu____1522
       then
         let uu____1525 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print1 "About to preprocess %s\n" uu____1525
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____1538 = traverse by_tactic_interp env goal in
       match uu____1538 with
       | (t',gs) ->
           ((let uu____1550 = FStar_ST.read FStar_Tactics_Basic.tacdbg in
             if uu____1550
             then
               let uu____1553 =
                 let uu____1554 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____1554
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____1555 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____1553 uu____1555
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____1574  ->
                    fun g  ->
                      match uu____1574 with
                      | (n1,gs1) ->
                          ((let uu____1595 =
                              FStar_ST.read FStar_Tactics_Basic.tacdbg in
                            if uu____1595
                            then
                              let uu____1598 = FStar_Util.string_of_int n1 in
                              let uu____1599 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____1598 uu____1599
                            else ());
                           (let gt' =
                              let uu____1602 =
                                let uu____1603 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Goal #" uu____1603 in
                              FStar_TypeChecker_Util.label uu____1602
                                FStar_Range.dummyRange
                                g.FStar_Tactics_Basic.goal_ty in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Basic.context), gt') ::
                              gs1))))) s gs in
             let uu____1609 = s1 in
             match uu____1609 with | (uu____1618,gs1) -> (env, t') :: gs1)))