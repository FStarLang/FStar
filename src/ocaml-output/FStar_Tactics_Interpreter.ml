open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let mk_tactic_interpretation_0:
  'a .
    'a FStar_Tactics_Basic.tac ->
      ('a -> FStar_Syntax_Syntax.term) ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lid ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun embed_a  ->
      fun t_a  ->
        fun nm  ->
          fun args  ->
            match args with
            | (embedded_state,uu____55)::[] ->
                let uu____72 =
                  FStar_Tactics_Embedding.unembed_proofstate embedded_state in
                FStar_Util.bind_opt uu____72
                  (fun ps  ->
                     FStar_Tactics_Basic.log ps
                       (fun uu____84  ->
                          let uu____85 = FStar_Ident.string_of_lid nm in
                          let uu____86 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.print2 "Reached %s, args are: %s\n"
                            uu____85 uu____86);
                     (let res = FStar_Tactics_Basic.run t ps in
                      let uu____90 =
                        FStar_Tactics_Embedding.embed_result ps res embed_a
                          t_a in
                      FStar_Pervasives_Native.Some uu____90))
            | uu____91 ->
                failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1:
  'a 'r .
    ('a -> 'r FStar_Tactics_Basic.tac) ->
      (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
        ('r -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun args  ->
              match args with
              | (a,uu____162)::(embedded_state,uu____164)::[] ->
                  let uu____191 =
                    FStar_Tactics_Embedding.unembed_proofstate embedded_state in
                  FStar_Util.bind_opt uu____191
                    (fun ps  ->
                       FStar_Tactics_Basic.log ps
                         (fun uu____202  ->
                            let uu____203 = FStar_Ident.string_of_lid nm in
                            let uu____204 =
                              FStar_Syntax_Print.term_to_string
                                embedded_state in
                            FStar_Util.print2 "Reached %s, goals are: %s\n"
                              uu____203 uu____204);
                       (let uu____205 = unembed_a a in
                        FStar_Util.bind_opt uu____205
                          (fun a1  ->
                             let res =
                               let uu____215 = t a1 in
                               FStar_Tactics_Basic.run uu____215 ps in
                             let uu____218 =
                               FStar_Tactics_Embedding.embed_result ps res
                                 embed_r t_r in
                             FStar_Pervasives_Native.Some uu____218)))
              | uu____219 ->
                  let uu____220 =
                    let uu____221 = FStar_Ident.string_of_lid nm in
                    let uu____222 = FStar_Syntax_Print.args_to_string args in
                    FStar_Util.format2
                      "Unexpected application of tactic primitive %s %s"
                      uu____221 uu____222 in
                  failwith uu____220
let mk_tactic_interpretation_1_env:
  'a 'b .
    (FStar_TypeChecker_Normalize.psc -> 'b -> 'a FStar_Tactics_Basic.tac) ->
      (FStar_Syntax_Syntax.term -> 'b FStar_Pervasives_Native.option) ->
        ('a -> FStar_Syntax_Syntax.term) ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_b  ->
      fun embed_a  ->
        fun t_a  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (b,uu____304)::(embedded_state,uu____306)::[] ->
                    let uu____333 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____333
                      (fun ps  ->
                         FStar_Tactics_Basic.log ps
                           (fun uu____344  ->
                              let uu____345 = FStar_Ident.string_of_lid nm in
                              let uu____346 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____345 uu____346);
                         (let uu____347 = unembed_b b in
                          FStar_Util.bind_opt uu____347
                            (fun b1  ->
                               let res =
                                 let uu____357 = t psc b1 in
                                 FStar_Tactics_Basic.run uu____357 ps in
                               let uu____360 =
                                 FStar_Tactics_Embedding.embed_result ps res
                                   embed_a t_a in
                               FStar_Pervasives_Native.Some uu____360)))
                | uu____361 ->
                    let uu____362 =
                      let uu____363 = FStar_Ident.string_of_lid nm in
                      let uu____364 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____363 uu____364 in
                    failwith uu____362
let mk_tactic_interpretation_2:
  'a 'b 'r .
    ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
      (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
        (FStar_Syntax_Syntax.term -> 'b FStar_Pervasives_Native.option) ->
          ('r -> FStar_Syntax_Syntax.term) ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun args  ->
                match args with
                | (a,uu____458)::(b,uu____460)::(embedded_state,uu____462)::[]
                    ->
                    let uu____499 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____499
                      (fun ps  ->
                         FStar_Tactics_Basic.log ps
                           (fun uu____510  ->
                              let uu____511 = FStar_Ident.string_of_lid nm in
                              let uu____512 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____511 uu____512);
                         (let uu____513 = unembed_a a in
                          FStar_Util.bind_opt uu____513
                            (fun a1  ->
                               let uu____519 = unembed_b b in
                               FStar_Util.bind_opt uu____519
                                 (fun b1  ->
                                    let res =
                                      let uu____529 = t a1 b1 in
                                      FStar_Tactics_Basic.run uu____529 ps in
                                    let uu____532 =
                                      FStar_Tactics_Embedding.embed_result ps
                                        res embed_r t_r in
                                    FStar_Pervasives_Native.Some uu____532))))
                | uu____533 ->
                    let uu____534 =
                      let uu____535 = FStar_Ident.string_of_lid nm in
                      let uu____536 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____535 uu____536 in
                    failwith uu____534
let mk_tactic_interpretation_3:
  'a 'b 'c 'r .
    ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
      (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
        (FStar_Syntax_Syntax.term -> 'b FStar_Pervasives_Native.option) ->
          (FStar_Syntax_Syntax.term -> 'c FStar_Pervasives_Native.option) ->
            ('r -> FStar_Syntax_Syntax.term) ->
              FStar_Syntax_Syntax.typ ->
                FStar_Ident.lid ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun unembed_c  ->
          fun embed_r  ->
            fun t_r  ->
              fun nm  ->
                fun args  ->
                  match args with
                  | (a,uu____653)::(b,uu____655)::(c,uu____657)::(embedded_state,uu____659)::[]
                      ->
                      let uu____706 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      FStar_Util.bind_opt uu____706
                        (fun ps  ->
                           FStar_Tactics_Basic.log ps
                             (fun uu____717  ->
                                let uu____718 = FStar_Ident.string_of_lid nm in
                                let uu____719 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____718
                                  uu____719);
                           (let uu____720 = unembed_a a in
                            FStar_Util.bind_opt uu____720
                              (fun a1  ->
                                 let uu____726 = unembed_b b in
                                 FStar_Util.bind_opt uu____726
                                   (fun b1  ->
                                      let uu____732 = unembed_c c in
                                      FStar_Util.bind_opt uu____732
                                        (fun c1  ->
                                           let res =
                                             let uu____742 = t a1 b1 c1 in
                                             FStar_Tactics_Basic.run
                                               uu____742 ps in
                                           let uu____745 =
                                             FStar_Tactics_Embedding.embed_result
                                               ps res embed_r t_r in
                                           FStar_Pervasives_Native.Some
                                             uu____745)))))
                  | uu____746 ->
                      let uu____747 =
                        let uu____748 = FStar_Ident.string_of_lid nm in
                        let uu____749 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____748 uu____749 in
                      failwith uu____747
let mk_tactic_interpretation_5:
  'a 'b 'c 'd 'e 'r .
    ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
      (FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option) ->
        (FStar_Syntax_Syntax.term -> 'b FStar_Pervasives_Native.option) ->
          (FStar_Syntax_Syntax.term -> 'c FStar_Pervasives_Native.option) ->
            (FStar_Syntax_Syntax.term -> 'd FStar_Pervasives_Native.option)
              ->
              (FStar_Syntax_Syntax.term -> 'e FStar_Pervasives_Native.option)
                ->
                ('r -> FStar_Syntax_Syntax.term) ->
                  FStar_Syntax_Syntax.typ ->
                    FStar_Ident.lid ->
                      FStar_Syntax_Syntax.args ->
                        FStar_Syntax_Syntax.term
                          FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun unembed_c  ->
          fun unembed_d  ->
            fun unembed_e  ->
              fun embed_r  ->
                fun t_r  ->
                  fun nm  ->
                    fun args  ->
                      match args with
                      | (a,uu____912)::(b,uu____914)::(c,uu____916)::
                          (d,uu____918)::(e,uu____920)::(embedded_state,uu____922)::[]
                          ->
                          let uu____989 =
                            FStar_Tactics_Embedding.unembed_proofstate
                              embedded_state in
                          FStar_Util.bind_opt uu____989
                            (fun ps  ->
                               FStar_Tactics_Basic.log ps
                                 (fun uu____1000  ->
                                    let uu____1001 =
                                      FStar_Ident.string_of_lid nm in
                                    let uu____1002 =
                                      FStar_Syntax_Print.term_to_string
                                        embedded_state in
                                    FStar_Util.print2
                                      "Reached %s, goals are: %s\n"
                                      uu____1001 uu____1002);
                               (let uu____1003 = unembed_a a in
                                FStar_Util.bind_opt uu____1003
                                  (fun a1  ->
                                     let uu____1009 = unembed_b b in
                                     FStar_Util.bind_opt uu____1009
                                       (fun b1  ->
                                          let uu____1015 = unembed_c c in
                                          FStar_Util.bind_opt uu____1015
                                            (fun c1  ->
                                               let uu____1021 = unembed_d d in
                                               FStar_Util.bind_opt uu____1021
                                                 (fun d1  ->
                                                    let uu____1027 =
                                                      unembed_e e in
                                                    FStar_Util.bind_opt
                                                      uu____1027
                                                      (fun e1  ->
                                                         let res =
                                                           let uu____1037 =
                                                             t a1 b1 c1 d1 e1 in
                                                           FStar_Tactics_Basic.run
                                                             uu____1037 ps in
                                                         let uu____1040 =
                                                           FStar_Tactics_Embedding.embed_result
                                                             ps res embed_r
                                                             t_r in
                                                         FStar_Pervasives_Native.Some
                                                           uu____1040)))))))
                      | uu____1041 ->
                          let uu____1042 =
                            let uu____1043 = FStar_Ident.string_of_lid nm in
                            let uu____1044 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.format2
                              "Unexpected application of tactic primitive %s %s"
                              uu____1043 uu____1044 in
                          failwith uu____1042
let step_from_native_step:
  FStar_Tactics_Native.native_primitive_step ->
    FStar_TypeChecker_Normalize.primitive_step
  =
  fun s  ->
    {
      FStar_TypeChecker_Normalize.name = (s.FStar_Tactics_Native.name);
      FStar_TypeChecker_Normalize.arity = (s.FStar_Tactics_Native.arity);
      FStar_TypeChecker_Normalize.strong_reduction_ok =
        (s.FStar_Tactics_Native.strong_reduction_ok);
      FStar_TypeChecker_Normalize.requires_binder_substitution = false;
      FStar_TypeChecker_Normalize.interpretation =
        (fun _psc  -> fun args  -> s.FStar_Tactics_Native.tactic args)
    }
let rec primitive_steps:
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list =
  fun uu____1095  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun _rng  -> fun args  -> interpretation nm1 args)
      } in
    let mk_env nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc  -> fun args  -> interpretation nm1 psc args)
      } in
    let native_tactics = FStar_Tactics_Native.list_all () in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics in
    let mktac0 name f e_r tr =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 f e_r tr) in
    let mktac1 name f u_a e_r tr =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 f u_a e_r tr) in
    let mktac1_env name f u_a e_b tb =
      mk_env name (Prims.parse_int "2")
        (mk_tactic_interpretation_1_env f u_a e_b tb) in
    let mktac2 name f u_a u_b e_r tr =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 f u_a u_b e_r tr) in
    let mktac3 name f u_a u_b u_c e_r tr =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 f u_a u_b u_c e_r tr) in
    let mktac5 name f u_a u_b u_c u_d u_e e_r tr =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 f u_a u_b u_c u_d u_e e_r tr) in
    let decr_depth_interp rng args =
      match args with
      | (ps,uu____1628)::[] ->
          let uu____1645 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1645
            (fun ps1  ->
               let uu____1651 =
                 let uu____1652 = FStar_Tactics_Types.decr_depth ps1 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1652 in
               FStar_Pervasives_Native.Some uu____1651)
      | uu____1653 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1657 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1657;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp rng args =
      match args with
      | (ps,uu____1670)::[] ->
          let uu____1687 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1687
            (fun ps1  ->
               let uu____1693 =
                 let uu____1694 = FStar_Tactics_Types.incr_depth ps1 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1694 in
               FStar_Pervasives_Native.Some uu____1693)
      | uu____1695 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1699 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1699;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp rng args =
      match args with
      | (ps,uu____1716)::[] ->
          let uu____1733 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1733
            (fun ps1  ->
               FStar_Tactics_Types.tracepoint ps1;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1744 -> failwith "Unexpected application of tracepoint" in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let uu____1751 =
      let uu____1754 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
      let uu____1755 =
        let uu____1758 =
          mktac2 "__trytac" (fun uu____1764  -> FStar_Tactics_Basic.trytac)
            (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
            (unembed_tactic_0'
               (fun _0_66  -> FStar_Pervasives_Native.Some _0_66))
            (FStar_Syntax_Embeddings.embed_option (fun t  -> t)
               FStar_Syntax_Syntax.t_unit) FStar_Syntax_Syntax.t_unit in
        let uu____1767 =
          let uu____1770 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1771 =
            let uu____1774 =
              let uu____1775 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec
                (FStar_Syntax_Embeddings.embed_pair
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder
                   FStar_Reflection_Basic.embed_binder
                   FStar_Reflection_Data.fstar_refl_binder) uu____1775 in
            let uu____1780 =
              let uu____1783 =
                mktac1 "__norm" FStar_Tactics_Basic.norm
                  (FStar_Syntax_Embeddings.unembed_list
                     FStar_Syntax_Embeddings.unembed_norm_step)
                  FStar_Syntax_Embeddings.embed_unit
                  FStar_Syntax_Syntax.t_unit in
              let uu____1786 =
                let uu____1789 =
                  mktac3 "__norm_term_env" FStar_Tactics_Basic.norm_term_env
                    FStar_Reflection_Basic.unembed_env
                    (FStar_Syntax_Embeddings.unembed_list
                       FStar_Syntax_Embeddings.unembed_norm_step)
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_term
                    FStar_Syntax_Syntax.t_term in
                let uu____1792 =
                  let uu____1795 =
                    mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Syntax_Embeddings.unembed_string
                      FStar_Syntax_Embeddings.embed_unit
                      FStar_Syntax_Syntax.t_unit in
                  let uu____1796 =
                    let uu____1799 =
                      mktac1 "__binder_retype"
                        FStar_Tactics_Basic.binder_retype
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1800 =
                      let uu____1803 =
                        mktac0 "__revert" FStar_Tactics_Basic.revert
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____1804 =
                        let uu____1807 =
                          mktac0 "__clear_top" FStar_Tactics_Basic.clear_top
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____1808 =
                          let uu____1811 =
                            mktac1 "__clear" FStar_Tactics_Basic.clear
                              FStar_Reflection_Basic.unembed_binder
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____1812 =
                            let uu____1815 =
                              mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                                FStar_Reflection_Basic.unembed_binder
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____1816 =
                              let uu____1819 =
                                mktac0 "__smt" FStar_Tactics_Basic.smt
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____1820 =
                                let uu____1823 =
                                  mktac1 "__exact" FStar_Tactics_Basic.exact
                                    FStar_Reflection_Basic.unembed_term
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____1824 =
                                  let uu____1827 =
                                    mktac1 "__apply"
                                      (FStar_Tactics_Basic.apply true)
                                      FStar_Reflection_Basic.unembed_term
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____1828 =
                                    let uu____1831 =
                                      mktac1 "__apply_raw"
                                        (FStar_Tactics_Basic.apply false)
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____1832 =
                                      let uu____1835 =
                                        mktac1 "__apply_lemma"
                                          FStar_Tactics_Basic.apply_lemma
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____1836 =
                                        let uu____1839 =
                                          mktac5 "__divide"
                                            (fun uu____1850  ->
                                               fun uu____1851  ->
                                                 FStar_Tactics_Basic.divide)
                                            (fun _0_67  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_67)
                                            (fun _0_68  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_68)
                                            FStar_Syntax_Embeddings.unembed_int
                                            (unembed_tactic_0'
                                               (fun _0_69  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_69))
                                            (unembed_tactic_0'
                                               (fun _0_70  ->
                                                  FStar_Pervasives_Native.Some
                                                    _0_70))
                                            (FStar_Syntax_Embeddings.embed_pair
                                               (fun t  -> t)
                                               FStar_Syntax_Syntax.t_unit
                                               (fun t  -> t)
                                               FStar_Syntax_Syntax.t_unit)
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____1856 =
                                          let uu____1859 =
                                            mktac1 "__set_options"
                                              FStar_Tactics_Basic.set_options
                                              FStar_Syntax_Embeddings.unembed_string
                                              FStar_Syntax_Embeddings.embed_unit
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____1860 =
                                            let uu____1863 =
                                              mktac2 "__seq"
                                                FStar_Tactics_Basic.seq
                                                (unembed_tactic_0'
                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                (unembed_tactic_0'
                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____1868 =
                                              let uu____1871 =
                                                mktac1 "__tc"
                                                  FStar_Tactics_Basic.tc
                                                  FStar_Reflection_Basic.unembed_term
                                                  FStar_Reflection_Basic.embed_term
                                                  FStar_Syntax_Syntax.t_term in
                                              let uu____1872 =
                                                let uu____1875 =
                                                  mktac1 "__unshelve"
                                                    FStar_Tactics_Basic.unshelve
                                                    FStar_Reflection_Basic.unembed_term
                                                    FStar_Syntax_Embeddings.embed_unit
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____1876 =
                                                  let uu____1879 =
                                                    mktac2 "__unquote"
                                                      FStar_Tactics_Basic.unquote
                                                      (fun _0_71  ->
                                                         FStar_Pervasives_Native.Some
                                                           _0_71)
                                                      FStar_Reflection_Basic.unembed_term
                                                      (fun t  -> t)
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____1882 =
                                                    let uu____1885 =
                                                      mktac1 "__prune"
                                                        FStar_Tactics_Basic.prune
                                                        FStar_Syntax_Embeddings.unembed_string
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____1886 =
                                                      let uu____1889 =
                                                        mktac1 "__addns"
                                                          FStar_Tactics_Basic.addns
                                                          FStar_Syntax_Embeddings.unembed_string
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____1890 =
                                                        let uu____1893 =
                                                          mktac1 "__print"
                                                            (fun x  ->
                                                               FStar_Tactics_Basic.tacprint
                                                                 x;
                                                               FStar_Tactics_Basic.ret
                                                                 ())
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____1898 =
                                                          let uu____1901 =
                                                            mktac1_env
                                                              "__dump"
                                                              FStar_Tactics_Basic.print_proof_state
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____1902 =
                                                            let uu____1905 =
                                                              mktac1_env
                                                                "__dump1"
                                                                FStar_Tactics_Basic.print_proof_state1
                                                                FStar_Syntax_Embeddings.unembed_string
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____1906 =
                                                              let uu____1909
                                                                =
                                                                mktac2
                                                                  "__pointwise"
                                                                  FStar_Tactics_Basic.pointwise
                                                                  FStar_Tactics_Embedding.unembed_direction
                                                                  (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____1912
                                                                =
                                                                let uu____1915
                                                                  =
                                                                  mktac0
                                                                    "__trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____1916
                                                                  =
                                                                  let uu____1919
                                                                    =
                                                                    mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____1920
                                                                    =
                                                                    let uu____1923
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1924
                                                                    =
                                                                    let uu____1927
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1928
                                                                    =
                                                                    let uu____1931
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1932
                                                                    =
                                                                    let uu____1935
                                                                    =
                                                                    let uu____1936
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    (FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term)
                                                                    uu____1936 in
                                                                    let uu____1941
                                                                    =
                                                                    let uu____1944
                                                                    =
                                                                    mktac0
                                                                    "__top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1945
                                                                    =
                                                                    let uu____1948
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1949
                                                                    =
                                                                    let uu____1952
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1953
                                                                    =
                                                                    let uu____1956
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1957
                                                                    =
                                                                    let uu____1960
                                                                    =
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    (FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1963
                                                                    =
                                                                    let uu____1966
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____1967
                                                                    =
                                                                    let uu____1970
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____1970;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step] in
                                                                    uu____1966
                                                                    ::
                                                                    uu____1967 in
                                                                    uu____1960
                                                                    ::
                                                                    uu____1963 in
                                                                    uu____1956
                                                                    ::
                                                                    uu____1957 in
                                                                    uu____1952
                                                                    ::
                                                                    uu____1953 in
                                                                    uu____1948
                                                                    ::
                                                                    uu____1949 in
                                                                    uu____1944
                                                                    ::
                                                                    uu____1945 in
                                                                    uu____1935
                                                                    ::
                                                                    uu____1941 in
                                                                    uu____1931
                                                                    ::
                                                                    uu____1932 in
                                                                    uu____1927
                                                                    ::
                                                                    uu____1928 in
                                                                    uu____1923
                                                                    ::
                                                                    uu____1924 in
                                                                  uu____1919
                                                                    ::
                                                                    uu____1920 in
                                                                uu____1915 ::
                                                                  uu____1916 in
                                                              uu____1909 ::
                                                                uu____1912 in
                                                            uu____1905 ::
                                                              uu____1906 in
                                                          uu____1901 ::
                                                            uu____1902 in
                                                        uu____1893 ::
                                                          uu____1898 in
                                                      uu____1889 ::
                                                        uu____1890 in
                                                    uu____1885 :: uu____1886 in
                                                  uu____1879 :: uu____1882 in
                                                uu____1875 :: uu____1876 in
                                              uu____1871 :: uu____1872 in
                                            uu____1863 :: uu____1868 in
                                          uu____1859 :: uu____1860 in
                                        uu____1839 :: uu____1856 in
                                      uu____1835 :: uu____1836 in
                                    uu____1831 :: uu____1832 in
                                  uu____1827 :: uu____1828 in
                                uu____1823 :: uu____1824 in
                              uu____1819 :: uu____1820 in
                            uu____1815 :: uu____1816 in
                          uu____1811 :: uu____1812 in
                        uu____1807 :: uu____1808 in
                      uu____1803 :: uu____1804 in
                    uu____1799 :: uu____1800 in
                  uu____1795 :: uu____1796 in
                uu____1789 :: uu____1792 in
              uu____1783 :: uu____1786 in
            uu____1774 :: uu____1780 in
          uu____1770 :: uu____1771 in
        uu____1758 :: uu____1767 in
      uu____1754 :: uu____1755 in
    FStar_List.append uu____1751
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0:
  'Ab .
    (FStar_Syntax_Syntax.term -> 'Ab FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let tm =
             let uu____1991 =
               let uu____1992 =
                 let uu____1993 =
                   let uu____1994 =
                     FStar_Tactics_Embedding.embed_proofstate proof_state in
                   FStar_Syntax_Syntax.as_arg uu____1994 in
                 [uu____1993] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____1992 in
             uu____1991 FStar_Pervasives_Native.None FStar_Range.dummyRange in
           let steps =
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2001 = FStar_ST.op_Bang tacdbg in
            if uu____2001
            then
              let uu____2048 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2048
            else ());
           (let result =
              let uu____2051 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2051 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2055 = FStar_ST.op_Bang tacdbg in
             if uu____2055
             then
               let uu____2102 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2102
             else ());
            (let uu____2104 =
               FStar_Tactics_Embedding.unembed_result proof_state result
                 unembed_b in
             match uu____2104 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2143 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2143
                   (fun uu____2147  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2170 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2170
                   (fun uu____2174  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2187 =
                   let uu____2188 =
                     let uu____2193 =
                       let uu____2194 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____2194 in
                     (uu____2193,
                       ((proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)) in
                   FStar_Errors.Error uu____2188 in
                 FStar_Exn.raise uu____2187)))
and unembed_tactic_0':
  'Ab .
    (FStar_Syntax_Syntax.term -> 'Ab FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2203 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_72  -> FStar_Pervasives_Native.Some _0_72)
        uu____2203
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2253  ->
             match uu____2253 with
             | (r,uu____2271,uv,uu____2273,ty,rng) ->
                 let uu____2276 =
                   let uu____2277 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2278 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2277 uu____2278 r in
                 (uu____2276, rng)) is in
      match errs with
      | [] -> ()
      | hd1::tl1 ->
          (FStar_Tactics_Basic.dump_proofstate ps
             "failing due to uninstantiated implicits";
           FStar_Errors.add_errors tl1;
           FStar_Exn.raise (FStar_Errors.Error hd1))
let run_tactic_on_typ:
  FStar_Syntax_Syntax.term ->
    FStar_Tactics_Basic.env ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Tactics_Types.goal Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun tactic  ->
    fun env  ->
      fun typ  ->
        (let uu____2326 = FStar_ST.op_Bang tacdbg in
         if uu____2326
         then
           let uu____2373 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2373
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         (let uu____2377 = FStar_ST.op_Bang tacdbg in
          if uu____2377
          then
            let uu____2424 = FStar_Syntax_Print.term_to_string tactic1 in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2424
          else ());
         (let uu____2426 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1 in
          match uu____2426 with
          | (tactic2,uu____2440,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic2 in
                let uu____2447 = FStar_TypeChecker_Env.clear_expected_typ env in
                match uu____2447 with
                | (env1,uu____2461) ->
                    let env2 =
                      let uu___165_2467 = env1 in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___165_2467.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___165_2467.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___165_2467.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___165_2467.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___165_2467.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___165_2467.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___165_2467.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___165_2467.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___165_2467.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___165_2467.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___165_2467.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___165_2467.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___165_2467.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___165_2467.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___165_2467.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___165_2467.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___165_2467.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___165_2467.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___165_2467.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___165_2467.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___165_2467.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___165_2467.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___165_2467.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___165_2467.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___165_2467.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qname_and_index =
                          (uu___165_2467.FStar_TypeChecker_Env.qname_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___165_2467.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___165_2467.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___165_2467.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___165_2467.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___165_2467.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___165_2467.FStar_TypeChecker_Env.dsenv)
                      } in
                    let uu____2468 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
                    (match uu____2468 with
                     | (ps,w) ->
                         ((let uu____2482 = FStar_ST.op_Bang tacdbg in
                           if uu____2482
                           then FStar_Util.print_string "Running tactic.\n"
                           else ());
                          (let uu____2530 = FStar_Tactics_Basic.run tau ps in
                           match uu____2530 with
                           | FStar_Tactics_Result.Success (uu____2539,ps1) ->
                               ((let uu____2542 = FStar_ST.op_Bang tacdbg in
                                 if uu____2542
                                 then
                                   let uu____2589 =
                                     FStar_Syntax_Print.term_to_string w in
                                   FStar_Util.print1
                                     "Tactic generated proofterm %s\n"
                                     uu____2589
                                 else ());
                                FStar_List.iter
                                  (fun g1  ->
                                     let uu____2596 =
                                       FStar_Tactics_Basic.is_irrelevant g1 in
                                     if uu____2596
                                     then
                                       let uu____2597 =
                                         FStar_TypeChecker_Rel.teq_nosmt
                                           g1.FStar_Tactics_Types.context
                                           g1.FStar_Tactics_Types.witness
                                           FStar_Syntax_Util.exp_unit in
                                       (if uu____2597
                                        then ()
                                        else
                                          (let uu____2599 =
                                             let uu____2600 =
                                               FStar_Syntax_Print.term_to_string
                                                 g1.FStar_Tactics_Types.witness in
                                             FStar_Util.format1
                                               "Irrelevant tactic witness does not unify with (): %s"
                                               uu____2600 in
                                           failwith uu____2599))
                                     else ())
                                  (FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals);
                                (let g1 =
                                   let uu___166_2603 =
                                     FStar_TypeChecker_Rel.trivial_guard in
                                   {
                                     FStar_TypeChecker_Env.guard_f =
                                       (uu___166_2603.FStar_TypeChecker_Env.guard_f);
                                     FStar_TypeChecker_Env.deferred =
                                       (uu___166_2603.FStar_TypeChecker_Env.deferred);
                                     FStar_TypeChecker_Env.univ_ineqs =
                                       (uu___166_2603.FStar_TypeChecker_Env.univ_ineqs);
                                     FStar_TypeChecker_Env.implicits =
                                       (ps1.FStar_Tactics_Types.all_implicits)
                                   } in
                                 let g2 =
                                   let uu____2605 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env2 g1 in
                                   FStar_All.pipe_right uu____2605
                                     FStar_TypeChecker_Rel.resolve_implicits_tac in
                                 report_implicits ps1
                                   g2.FStar_TypeChecker_Env.implicits;
                                 ((FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals), w)))
                           | FStar_Tactics_Result.Failed (s,ps1) ->
                               (FStar_Tactics_Basic.dump_proofstate ps1
                                  "at the time of failure";
                                (let uu____2612 =
                                   let uu____2613 =
                                     let uu____2618 =
                                       FStar_Util.format1
                                         "user tactic failed: %s" s in
                                     (uu____2618,
                                       (typ.FStar_Syntax_Syntax.pos)) in
                                   FStar_Errors.Error uu____2613 in
                                 FStar_Exn.raise uu____2612)))))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2629 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2634 -> false
let flip: pol -> pol = fun p  -> match p with | Pos  -> Neg | Neg  -> Pos
let by_tactic_interp:
  pol ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Tactics_Types.goal Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2663 = FStar_Syntax_Util.head_and_args t in
        match uu____2663 with
        | (hd1,args) ->
            let uu____2706 =
              let uu____2719 =
                let uu____2720 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2720.FStar_Syntax_Syntax.n in
              (uu____2719, args) in
            (match uu____2706 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2739))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2808 = run_tactic_on_typ tactic e assertion in
                   (match uu____2808 with
                    | (gs,uu____2822) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2874 =
                     let uu____2877 =
                       let uu____2878 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____2878 in
                     [uu____2877] in
                   (FStar_Syntax_Util.t_true, uu____2874)
                 else (assertion, [])
             | uu____2894 -> (t, []))
let rec traverse:
  (pol ->
     FStar_TypeChecker_Env.env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term,FStar_Tactics_Types.goal Prims.list)
           FStar_Pervasives_Native.tuple2)
    ->
    pol ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Tactics_Types.goal Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let uu____2964 =
            let uu____2971 =
              let uu____2972 = FStar_Syntax_Subst.compress t in
              uu____2972.FStar_Syntax_Syntax.n in
            match uu____2971 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____2987 = traverse f pol e t1 in
                (match uu____2987 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____3014 = traverse f pol e t1 in
                (match uu____3014 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3036;
                   FStar_Syntax_Syntax.vars = uu____3037;_},(p,uu____3039)::
                 (q,uu____3041)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3081 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3081 in
                let uu____3082 = traverse f (flip pol) e p in
                (match uu____3082 with
                 | (p',gs1) ->
                     let uu____3101 =
                       let uu____3108 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____3108 q in
                     (match uu____3101 with
                      | (q',gs2) ->
                          let uu____3121 =
                            let uu____3122 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____3122.FStar_Syntax_Syntax.n in
                          (uu____3121, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____3149 = traverse f pol e hd1 in
                (match uu____3149 with
                 | (hd',gs1) ->
                     let uu____3168 =
                       FStar_List.fold_right
                         (fun uu____3206  ->
                            fun uu____3207  ->
                              match (uu____3206, uu____3207) with
                              | ((a,q),(as',gs)) ->
                                  let uu____3288 = traverse f pol e a in
                                  (match uu____3288 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____3168 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____3392 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____3392 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____3406 =
                       let uu____3421 =
                         FStar_List.map
                           (fun uu____3454  ->
                              match uu____3454 with
                              | (bv,aq) ->
                                  let uu____3471 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____3471 with
                                   | (s',gs) ->
                                       (((let uu___167_3501 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___167_3501.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___167_3501.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____3421 in
                     (match uu____3406 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____3565 = traverse f pol e' topen in
                          (match uu____3565 with
                           | (topen',gs2) ->
                               let uu____3584 =
                                 let uu____3585 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____3585.FStar_Syntax_Syntax.n in
                               (uu____3584, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____2964 with
          | (tn',gs) ->
              let t' =
                let uu___168_3608 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___168_3608.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___168_3608.FStar_Syntax_Syntax.vars)
                } in
              let uu____3609 = f pol e t' in
              (match uu____3609 with
               | (t'1,gs') -> (t'1, (FStar_List.append gs gs')))
let getprop:
  FStar_Tactics_Basic.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun e  ->
    fun t  ->
      let tn =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant] e t in
      FStar_Syntax_Util.un_squash tn
let preprocess:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env,FStar_Syntax_Syntax.term,FStar_Options.optionstate)
        FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun env  ->
    fun goal  ->
      (let uu____3668 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3668);
      (let uu____3716 = FStar_ST.op_Bang tacdbg in
       if uu____3716
       then
         let uu____3763 =
           let uu____3764 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____3764
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____3765 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3763
           uu____3765
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____3794 = traverse by_tactic_interp Pos env goal in
       match uu____3794 with
       | (t',gs) ->
           ((let uu____3816 = FStar_ST.op_Bang tacdbg in
             if uu____3816
             then
               let uu____3863 =
                 let uu____3864 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____3864
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____3865 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3863 uu____3865
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3912  ->
                    fun g  ->
                      match uu____3912 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____3957 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____3957 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____3960 =
                                  let uu____3961 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____3961 in
                                failwith uu____3960
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____3964 = FStar_ST.op_Bang tacdbg in
                            if uu____3964
                            then
                              let uu____4011 = FStar_Util.string_of_int n1 in
                              let uu____4012 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4011 uu____4012
                            else ());
                           (let gt' =
                              let uu____4015 =
                                let uu____4016 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4016 in
                              FStar_TypeChecker_Util.label uu____4015
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4031 = s1 in
             match uu____4031 with
             | (uu____4052,gs1) ->
                 let uu____4070 =
                   let uu____4077 = FStar_Options.peek () in
                   (env, t', uu____4077) in
                 uu____4070 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4089 =
        let uu____4090 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4090 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4089 [FStar_Syntax_Syntax.U_zero] in
    let uu____4091 =
      let uu____4092 =
        let uu____4093 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4094 =
          let uu____4097 = FStar_Syntax_Syntax.as_arg a in [uu____4097] in
        uu____4093 :: uu____4094 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4092 in
    uu____4091 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4113 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4113);
        (let uu____4160 =
           let uu____4167 = reify_tactic tau in
           run_tactic_on_typ uu____4167 env typ in
         match uu____4160 with
         | (gs,w) ->
             let uu____4174 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4178 =
                      let uu____4179 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4179 in
                    Prims.op_Negation uu____4178) gs in
             if uu____4174
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)