open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let mk_tactic_interpretation_0:
  'r .
    'r FStar_Tactics_Basic.tac ->
      'r FStar_Syntax_Embeddings.embedder ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lid ->
            FStar_Range.range ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun embed_r  ->
      fun t_r  ->
        fun nm  ->
          fun rng  ->
            fun args  ->
              match args with
              | (embedded_state,uu____66)::[] ->
                  let uu____83 =
                    FStar_Tactics_Embedding.unembed_proofstate embedded_state in
                  FStar_Util.bind_opt uu____83
                    (fun ps  ->
                       FStar_Tactics_Basic.log ps
                         (fun uu____95  ->
                            let uu____96 = FStar_Ident.string_of_lid nm in
                            let uu____97 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____96 uu____97);
                       (let res = FStar_Tactics_Basic.run t ps in
                        let uu____101 =
                          FStar_Tactics_Embedding.embed_result embed_r t_r
                            rng res in
                        FStar_Pervasives_Native.Some uu____101))
              | uu____108 ->
                  failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1:
  'a 'r .
    ('a -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'r FStar_Syntax_Embeddings.embedder ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_Range.range ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun rng  ->
              fun args  ->
                match args with
                | (a,uu____189)::(embedded_state,uu____191)::[] ->
                    let uu____218 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____218
                      (fun ps  ->
                         FStar_Tactics_Basic.log ps
                           (fun uu____229  ->
                              let uu____230 = FStar_Ident.string_of_lid nm in
                              let uu____231 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____230 uu____231);
                         (let uu____232 = unembed_a a in
                          FStar_Util.bind_opt uu____232
                            (fun a1  ->
                               let res =
                                 let uu____244 = t a1 in
                                 FStar_Tactics_Basic.run uu____244 ps in
                               let uu____247 =
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r rng res in
                               FStar_Pervasives_Native.Some uu____247)))
                | uu____254 ->
                    let uu____255 =
                      let uu____256 = FStar_Ident.string_of_lid nm in
                      let uu____257 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____256 uu____257 in
                    failwith uu____255
let mk_tactic_interpretation_2:
  'a 'b 'r .
    ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'b FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_Range.range ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun rng  ->
                fun args  ->
                  match args with
                  | (a,uu____360)::(b,uu____362)::(embedded_state,uu____364)::[]
                      ->
                      let uu____401 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      FStar_Util.bind_opt uu____401
                        (fun ps  ->
                           FStar_Tactics_Basic.log ps
                             (fun uu____412  ->
                                let uu____413 = FStar_Ident.string_of_lid nm in
                                let uu____414 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____413
                                  uu____414);
                           (let uu____415 = unembed_a a in
                            FStar_Util.bind_opt uu____415
                              (fun a1  ->
                                 let uu____423 = unembed_b b in
                                 FStar_Util.bind_opt uu____423
                                   (fun b1  ->
                                      let res =
                                        let uu____435 = t a1 b1 in
                                        FStar_Tactics_Basic.run uu____435 ps in
                                      let uu____438 =
                                        FStar_Tactics_Embedding.embed_result
                                          embed_r t_r rng res in
                                      FStar_Pervasives_Native.Some uu____438))))
                  | uu____445 ->
                      let uu____446 =
                        let uu____447 = FStar_Ident.string_of_lid nm in
                        let uu____448 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____447 uu____448 in
                      failwith uu____446
let mk_tactic_interpretation_3:
  'a 'b 'c 'r .
    ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'b FStar_Syntax_Embeddings.unembedder ->
          'c FStar_Syntax_Embeddings.unembedder ->
            'r FStar_Syntax_Embeddings.embedder ->
              FStar_Syntax_Syntax.typ ->
                FStar_Ident.lid ->
                  FStar_Range.range ->
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
                fun rng  ->
                  fun args  ->
                    match args with
                    | (a,uu____573)::(b,uu____575)::(c,uu____577)::(embedded_state,uu____579)::[]
                        ->
                        let uu____626 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        FStar_Util.bind_opt uu____626
                          (fun ps  ->
                             FStar_Tactics_Basic.log ps
                               (fun uu____637  ->
                                  let uu____638 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____639 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____638
                                    uu____639);
                             (let uu____640 = unembed_a a in
                              FStar_Util.bind_opt uu____640
                                (fun a1  ->
                                   let uu____648 = unembed_b b in
                                   FStar_Util.bind_opt uu____648
                                     (fun b1  ->
                                        let uu____656 = unembed_c c in
                                        FStar_Util.bind_opt uu____656
                                          (fun c1  ->
                                             let res =
                                               let uu____668 = t a1 b1 c1 in
                                               FStar_Tactics_Basic.run
                                                 uu____668 ps in
                                             let uu____671 =
                                               FStar_Tactics_Embedding.embed_result
                                                 embed_r t_r rng res in
                                             FStar_Pervasives_Native.Some
                                               uu____671)))))
                    | uu____678 ->
                        let uu____679 =
                          let uu____680 = FStar_Ident.string_of_lid nm in
                          let uu____681 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____680 uu____681 in
                        failwith uu____679
let mk_tactic_interpretation_5:
  'a 'b 'c 'd 'e 'r .
    ('a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'b FStar_Syntax_Embeddings.unembedder ->
          'c FStar_Syntax_Embeddings.unembedder ->
            'd FStar_Syntax_Embeddings.unembedder ->
              'e FStar_Syntax_Embeddings.unembedder ->
                'r FStar_Syntax_Embeddings.embedder ->
                  FStar_Syntax_Syntax.typ ->
                    FStar_Ident.lid ->
                      FStar_Range.range ->
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
                    fun rng  ->
                      fun args  ->
                        match args with
                        | (a,uu____850)::(b,uu____852)::(c,uu____854)::
                            (d,uu____856)::(e,uu____858)::(embedded_state,uu____860)::[]
                            ->
                            let uu____927 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state in
                            FStar_Util.bind_opt uu____927
                              (fun ps  ->
                                 FStar_Tactics_Basic.log ps
                                   (fun uu____938  ->
                                      let uu____939 =
                                        FStar_Ident.string_of_lid nm in
                                      let uu____940 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____939 uu____940);
                                 (let uu____941 = unembed_a a in
                                  FStar_Util.bind_opt uu____941
                                    (fun a1  ->
                                       let uu____949 = unembed_b b in
                                       FStar_Util.bind_opt uu____949
                                         (fun b1  ->
                                            let uu____957 = unembed_c c in
                                            FStar_Util.bind_opt uu____957
                                              (fun c1  ->
                                                 let uu____965 = unembed_d d in
                                                 FStar_Util.bind_opt
                                                   uu____965
                                                   (fun d1  ->
                                                      let uu____973 =
                                                        unembed_e e in
                                                      FStar_Util.bind_opt
                                                        uu____973
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____985 =
                                                               t a1 b1 c1 d1
                                                                 e1 in
                                                             FStar_Tactics_Basic.run
                                                               uu____985 ps in
                                                           let uu____988 =
                                                             FStar_Tactics_Embedding.embed_result
                                                               embed_r t_r
                                                               rng res in
                                                           FStar_Pervasives_Native.Some
                                                             uu____988)))))))
                        | uu____995 ->
                            let uu____996 =
                              let uu____997 = FStar_Ident.string_of_lid nm in
                              let uu____998 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____997 uu____998 in
                            failwith uu____996
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
      FStar_TypeChecker_Normalize.interpretation =
        (fun _rng  -> fun args  -> s.FStar_Tactics_Native.tactic args)
    }
let rec primitive_steps:
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list =
  fun uu____1051  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
      let uu____1084 = interpretation nm1 in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = uu____1084
      } in
    let native_tactics = FStar_Tactics_Native.list_all () in
    let native_tactics_steps =
      FStar_List.map step_from_native_step native_tactics in
    let mktac0 name f e_r tr =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 f e_r tr) in
    let mktac1 name f u_a e_r tr =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 f u_a e_r tr) in
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
      | (ps,uu____1588)::[] ->
          let uu____1605 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1605
            (fun ps1  ->
               let uu____1611 =
                 let uu____1612 = FStar_Tactics_Types.decr_depth ps1 in
                 FStar_Tactics_Embedding.embed_proofstate rng uu____1612 in
               FStar_Pervasives_Native.Some uu____1611)
      | uu____1613 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1617 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1617;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp rng args =
      match args with
      | (ps,uu____1630)::[] ->
          let uu____1647 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1647
            (fun ps1  ->
               let uu____1653 =
                 let uu____1654 = FStar_Tactics_Types.incr_depth ps1 in
                 FStar_Tactics_Embedding.embed_proofstate rng uu____1654 in
               FStar_Pervasives_Native.Some uu____1653)
      | uu____1655 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1659 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1659;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp rng args =
      match args with
      | (ps,uu____1676)::[] ->
          let uu____1693 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1693
            (fun ps1  ->
               FStar_Tactics_Types.tracepoint ps1;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1704 -> failwith "Unexpected application of tracepoint" in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let put1 rng t = t in
    let get1 t = FStar_Pervasives_Native.Some t in
    let uu____1724 =
      let uu____1727 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
      let uu____1728 =
        let uu____1731 =
          let uu____1732 =
            FStar_Syntax_Embeddings.embed_option put1
              FStar_Syntax_Syntax.t_unit in
          mktac2 "__trytac" (fun uu____1742  -> FStar_Tactics_Basic.trytac)
            get1 (unembed_tactic_0' get1) uu____1732
            FStar_Syntax_Syntax.t_unit in
        let uu____1749 =
          let uu____1752 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____1753 =
            let uu____1756 =
              let uu____1757 =
                FStar_Syntax_Embeddings.embed_pair
                  FStar_Reflection_Basic.embed_binder
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Basic.embed_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              let uu____1764 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec uu____1757
                uu____1764 in
            let uu____1775 =
              let uu____1778 =
                let uu____1779 =
                  FStar_Syntax_Embeddings.unembed_list
                    FStar_Syntax_Embeddings.unembed_norm_step in
                mktac1 "__norm" FStar_Tactics_Basic.norm uu____1779
                  FStar_Syntax_Embeddings.embed_unit
                  FStar_Syntax_Syntax.t_unit in
              let uu____1790 =
                let uu____1793 =
                  let uu____1794 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step in
                  mktac3 "__norm_term_env" FStar_Tactics_Basic.norm_term_env
                    FStar_Reflection_Basic.unembed_env uu____1794
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_term
                    FStar_Syntax_Syntax.t_term in
                let uu____1805 =
                  let uu____1808 =
                    mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Syntax_Embeddings.unembed_string
                      FStar_Syntax_Embeddings.embed_unit
                      FStar_Syntax_Syntax.t_unit in
                  let uu____1809 =
                    let uu____1812 =
                      mktac1 "__binder_retype"
                        FStar_Tactics_Basic.binder_retype
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1813 =
                      let uu____1816 =
                        mktac0 "__revert" FStar_Tactics_Basic.revert
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____1817 =
                        let uu____1820 =
                          mktac0 "__clear_top" FStar_Tactics_Basic.clear_top
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____1821 =
                          let uu____1824 =
                            mktac1 "__clear" FStar_Tactics_Basic.clear
                              FStar_Reflection_Basic.unembed_binder
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____1825 =
                            let uu____1828 =
                              mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                                FStar_Reflection_Basic.unembed_binder
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____1829 =
                              let uu____1832 =
                                mktac0 "__smt" FStar_Tactics_Basic.smt
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____1833 =
                                let uu____1836 =
                                  mktac1 "__exact" FStar_Tactics_Basic.exact
                                    FStar_Reflection_Basic.unembed_term
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____1837 =
                                  let uu____1840 =
                                    mktac1 "__apply"
                                      (FStar_Tactics_Basic.apply true)
                                      FStar_Reflection_Basic.unembed_term
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____1841 =
                                    let uu____1844 =
                                      mktac1 "__apply_raw"
                                        (FStar_Tactics_Basic.apply false)
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____1845 =
                                      let uu____1848 =
                                        mktac1 "__apply_lemma"
                                          FStar_Tactics_Basic.apply_lemma
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____1849 =
                                        let uu____1852 =
                                          let uu____1853 =
                                            FStar_Syntax_Embeddings.embed_pair
                                              put1 FStar_Syntax_Syntax.t_unit
                                              put1 FStar_Syntax_Syntax.t_unit in
                                          mktac5 "__divide"
                                            (fun uu____1870  ->
                                               fun uu____1871  ->
                                                 FStar_Tactics_Basic.divide)
                                            get1 get1
                                            FStar_Syntax_Embeddings.unembed_int
                                            (unembed_tactic_0' get1)
                                            (unembed_tactic_0' get1)
                                            uu____1853
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____1878 =
                                          let uu____1881 =
                                            mktac1 "__set_options"
                                              FStar_Tactics_Basic.set_options
                                              FStar_Syntax_Embeddings.unembed_string
                                              FStar_Syntax_Embeddings.embed_unit
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____1882 =
                                            let uu____1885 =
                                              mktac2 "__seq"
                                                FStar_Tactics_Basic.seq
                                                (unembed_tactic_0'
                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                (unembed_tactic_0'
                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____1890 =
                                              let uu____1893 =
                                                mktac1 "__tc"
                                                  FStar_Tactics_Basic.tc
                                                  FStar_Reflection_Basic.unembed_term
                                                  FStar_Reflection_Basic.embed_term
                                                  FStar_Syntax_Syntax.t_term in
                                              let uu____1894 =
                                                let uu____1897 =
                                                  mktac1 "__unshelve"
                                                    FStar_Tactics_Basic.unshelve
                                                    FStar_Reflection_Basic.unembed_term
                                                    FStar_Syntax_Embeddings.embed_unit
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____1898 =
                                                  let uu____1901 =
                                                    mktac2 "__unquote"
                                                      FStar_Tactics_Basic.unquote
                                                      get1
                                                      FStar_Reflection_Basic.unembed_term
                                                      put1
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____1902 =
                                                    let uu____1905 =
                                                      mktac1 "__prune"
                                                        FStar_Tactics_Basic.prune
                                                        FStar_Syntax_Embeddings.unembed_string
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____1906 =
                                                      let uu____1909 =
                                                        mktac1 "__addns"
                                                          FStar_Tactics_Basic.addns
                                                          FStar_Syntax_Embeddings.unembed_string
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____1910 =
                                                        let uu____1913 =
                                                          mktac1 "__print"
                                                            (fun x  ->
                                                               FStar_Tactics_Basic.tacprint
                                                                 x;
                                                               FStar_Tactics_Basic.ret
                                                                 ())
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____1918 =
                                                          let uu____1921 =
                                                            mktac1 "__dump"
                                                              FStar_Tactics_Basic.print_proof_state
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____1922 =
                                                            let uu____1925 =
                                                              mktac1
                                                                "__dump1"
                                                                FStar_Tactics_Basic.print_proof_state1
                                                                FStar_Syntax_Embeddings.unembed_string
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____1926 =
                                                              let uu____1929
                                                                =
                                                                mktac2
                                                                  "__pointwise"
                                                                  FStar_Tactics_Basic.pointwise
                                                                  FStar_Tactics_Embedding.unembed_direction
                                                                  (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____1932
                                                                =
                                                                let uu____1935
                                                                  =
                                                                  mktac0
                                                                    "__trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____1936
                                                                  =
                                                                  let uu____1939
                                                                    =
                                                                    mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____1940
                                                                    =
                                                                    let uu____1943
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1944
                                                                    =
                                                                    let uu____1947
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1948
                                                                    =
                                                                    let uu____1951
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____1952
                                                                    =
                                                                    let uu____1955
                                                                    =
                                                                    let uu____1956
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1963
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    uu____1956
                                                                    uu____1963 in
                                                                    let uu____1974
                                                                    =
                                                                    let uu____1977
                                                                    =
                                                                    mktac0
                                                                    "__top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1978
                                                                    =
                                                                    let uu____1981
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____1982
                                                                    =
                                                                    let uu____1985
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1986
                                                                    =
                                                                    let uu____1989
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____1990
                                                                    =
                                                                    let uu____1993
                                                                    =
                                                                    let uu____1994
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term in
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    uu____1994
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2005
                                                                    =
                                                                    let uu____2008
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2009
                                                                    =
                                                                    let uu____2012
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____2012;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step] in
                                                                    uu____2008
                                                                    ::
                                                                    uu____2009 in
                                                                    uu____1993
                                                                    ::
                                                                    uu____2005 in
                                                                    uu____1989
                                                                    ::
                                                                    uu____1990 in
                                                                    uu____1985
                                                                    ::
                                                                    uu____1986 in
                                                                    uu____1981
                                                                    ::
                                                                    uu____1982 in
                                                                    uu____1977
                                                                    ::
                                                                    uu____1978 in
                                                                    uu____1955
                                                                    ::
                                                                    uu____1974 in
                                                                    uu____1951
                                                                    ::
                                                                    uu____1952 in
                                                                    uu____1947
                                                                    ::
                                                                    uu____1948 in
                                                                    uu____1943
                                                                    ::
                                                                    uu____1944 in
                                                                  uu____1939
                                                                    ::
                                                                    uu____1940 in
                                                                uu____1935 ::
                                                                  uu____1936 in
                                                              uu____1929 ::
                                                                uu____1932 in
                                                            uu____1925 ::
                                                              uu____1926 in
                                                          uu____1921 ::
                                                            uu____1922 in
                                                        uu____1913 ::
                                                          uu____1918 in
                                                      uu____1909 ::
                                                        uu____1910 in
                                                    uu____1905 :: uu____1906 in
                                                  uu____1901 :: uu____1902 in
                                                uu____1897 :: uu____1898 in
                                              uu____1893 :: uu____1894 in
                                            uu____1885 :: uu____1890 in
                                          uu____1881 :: uu____1882 in
                                        uu____1852 :: uu____1878 in
                                      uu____1848 :: uu____1849 in
                                    uu____1844 :: uu____1845 in
                                  uu____1840 :: uu____1841 in
                                uu____1836 :: uu____1837 in
                              uu____1832 :: uu____1833 in
                            uu____1828 :: uu____1829 in
                          uu____1824 :: uu____1825 in
                        uu____1820 :: uu____1821 in
                      uu____1816 :: uu____1817 in
                    uu____1812 :: uu____1813 in
                  uu____1808 :: uu____1809 in
                uu____1793 :: uu____1805 in
              uu____1778 :: uu____1790 in
            uu____1756 :: uu____1775 in
          uu____1752 :: uu____1753 in
        uu____1731 :: uu____1749 in
      uu____1727 :: uu____1728 in
    FStar_List.append uu____1724
      (FStar_List.append FStar_Reflection_Interpreter.reflection_primops
         native_tactics_steps)
and unembed_tactic_0:
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term -> 'Ab FStar_Tactics_Basic.tac
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      FStar_Tactics_Basic.bind FStar_Tactics_Basic.get
        (fun proof_state  ->
           let rng = embedded_tac_b.FStar_Syntax_Syntax.pos in
           let tm =
             let uu____2035 =
               let uu____2036 =
                 let uu____2037 =
                   let uu____2038 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____2038 in
                 [uu____2037] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2036 in
             uu____2035 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2045 = FStar_ST.op_Bang tacdbg in
            if uu____2045
            then
              let uu____2092 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2092
            else ());
           (let result =
              let uu____2095 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2095 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2099 = FStar_ST.op_Bang tacdbg in
             if uu____2099
             then
               let uu____2146 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2146
             else ());
            (let uu____2148 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2148 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2191 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2191
                   (fun uu____2195  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2218 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2218
                   (fun uu____2222  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2235 =
                   let uu____2236 =
                     let uu____2241 =
                       let uu____2242 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____2242 in
                     (uu____2241,
                       ((proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)) in
                   FStar_Errors.Error uu____2236 in
                 FStar_Exn.raise uu____2235)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2251 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
        uu____2251
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2305  ->
             match uu____2305 with
             | (r,uu____2323,uv,uu____2325,ty,rng) ->
                 let uu____2328 =
                   let uu____2329 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2330 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2329 uu____2330 r in
                 (uu____2328, rng)) is in
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
        (let uu____2378 = FStar_ST.op_Bang tacdbg in
         if uu____2378
         then
           let uu____2425 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2425
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         (let uu____2429 = FStar_ST.op_Bang tacdbg in
          if uu____2429
          then
            let uu____2476 = FStar_Syntax_Print.term_to_string tactic1 in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2476
          else ());
         (let uu____2478 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1 in
          match uu____2478 with
          | (tactic2,uu____2492,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic2 in
                let uu____2499 = FStar_TypeChecker_Env.clear_expected_typ env in
                match uu____2499 with
                | (env1,uu____2513) ->
                    let env2 =
                      let uu___170_2519 = env1 in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___170_2519.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___170_2519.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___170_2519.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___170_2519.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___170_2519.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___170_2519.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___170_2519.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___170_2519.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___170_2519.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___170_2519.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___170_2519.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___170_2519.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___170_2519.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___170_2519.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___170_2519.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___170_2519.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___170_2519.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___170_2519.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___170_2519.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___170_2519.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___170_2519.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___170_2519.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___170_2519.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___170_2519.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___170_2519.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qname_and_index =
                          (uu___170_2519.FStar_TypeChecker_Env.qname_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___170_2519.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___170_2519.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___170_2519.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___170_2519.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___170_2519.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___170_2519.FStar_TypeChecker_Env.dsenv)
                      } in
                    let uu____2520 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
                    (match uu____2520 with
                     | (ps,w) ->
                         ((let uu____2534 = FStar_ST.op_Bang tacdbg in
                           if uu____2534
                           then
                             let uu____2581 =
                               FStar_Syntax_Print.term_to_string typ in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2581
                           else ());
                          (let uu____2583 = FStar_Tactics_Basic.run tau ps in
                           match uu____2583 with
                           | FStar_Tactics_Result.Success (uu____2592,ps1) ->
                               ((let uu____2595 = FStar_ST.op_Bang tacdbg in
                                 if uu____2595
                                 then
                                   let uu____2642 =
                                     FStar_Syntax_Print.term_to_string w in
                                   FStar_Util.print1
                                     "Tactic generated proofterm %s\n"
                                     uu____2642
                                 else ());
                                FStar_List.iter
                                  (fun g1  ->
                                     let uu____2649 =
                                       FStar_Tactics_Basic.is_irrelevant g1 in
                                     if uu____2649
                                     then
                                       let uu____2650 =
                                         FStar_TypeChecker_Rel.teq_nosmt
                                           g1.FStar_Tactics_Types.context
                                           g1.FStar_Tactics_Types.witness
                                           FStar_Syntax_Util.exp_unit in
                                       (if uu____2650
                                        then ()
                                        else
                                          (let uu____2652 =
                                             let uu____2653 =
                                               FStar_Syntax_Print.term_to_string
                                                 g1.FStar_Tactics_Types.witness in
                                             FStar_Util.format1
                                               "Irrelevant tactic witness does not unify with (): %s"
                                               uu____2653 in
                                           failwith uu____2652))
                                     else ())
                                  (FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals);
                                (let g1 =
                                   let uu___171_2656 =
                                     FStar_TypeChecker_Rel.trivial_guard in
                                   {
                                     FStar_TypeChecker_Env.guard_f =
                                       (uu___171_2656.FStar_TypeChecker_Env.guard_f);
                                     FStar_TypeChecker_Env.deferred =
                                       (uu___171_2656.FStar_TypeChecker_Env.deferred);
                                     FStar_TypeChecker_Env.univ_ineqs =
                                       (uu___171_2656.FStar_TypeChecker_Env.univ_ineqs);
                                     FStar_TypeChecker_Env.implicits =
                                       (ps1.FStar_Tactics_Types.all_implicits)
                                   } in
                                 let g2 =
                                   let uu____2658 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env2 g1 in
                                   FStar_All.pipe_right uu____2658
                                     FStar_TypeChecker_Rel.resolve_implicits_tac in
                                 report_implicits ps1
                                   g2.FStar_TypeChecker_Env.implicits;
                                 ((FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals), w)))
                           | FStar_Tactics_Result.Failed (s,ps1) ->
                               (FStar_Tactics_Basic.dump_proofstate ps1
                                  "at the time of failure";
                                (let uu____2665 =
                                   let uu____2666 =
                                     let uu____2671 =
                                       FStar_Util.format1
                                         "user tactic failed: %s" s in
                                     (uu____2671,
                                       (typ.FStar_Syntax_Syntax.pos)) in
                                   FStar_Errors.Error uu____2666 in
                                 FStar_Exn.raise uu____2665)))))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2682 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2687 -> false
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
        let uu____2716 = FStar_Syntax_Util.head_and_args t in
        match uu____2716 with
        | (hd1,args) ->
            let uu____2759 =
              let uu____2772 =
                let uu____2773 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2773.FStar_Syntax_Syntax.n in
              (uu____2772, args) in
            (match uu____2759 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2792))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2861 = run_tactic_on_typ tactic e assertion in
                   (match uu____2861 with
                    | (gs,uu____2875) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2927 =
                     let uu____2930 =
                       let uu____2931 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____2931 in
                     [uu____2930] in
                   (FStar_Syntax_Util.t_true, uu____2927)
                 else (assertion, [])
             | uu____2947 -> (t, []))
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
          let uu____3017 =
            let uu____3024 =
              let uu____3025 = FStar_Syntax_Subst.compress t in
              uu____3025.FStar_Syntax_Syntax.n in
            match uu____3024 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____3040 = traverse f pol e t1 in
                (match uu____3040 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____3067 = traverse f pol e t1 in
                (match uu____3067 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3089;
                   FStar_Syntax_Syntax.vars = uu____3090;_},(p,uu____3092)::
                 (q,uu____3094)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3134 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3134 in
                let uu____3135 = traverse f (flip pol) e p in
                (match uu____3135 with
                 | (p',gs1) ->
                     let uu____3154 =
                       let uu____3161 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____3161 q in
                     (match uu____3154 with
                      | (q',gs2) ->
                          let uu____3174 =
                            let uu____3175 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____3175.FStar_Syntax_Syntax.n in
                          (uu____3174, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____3202 = traverse f pol e hd1 in
                (match uu____3202 with
                 | (hd',gs1) ->
                     let uu____3221 =
                       FStar_List.fold_right
                         (fun uu____3259  ->
                            fun uu____3260  ->
                              match (uu____3259, uu____3260) with
                              | ((a,q),(as',gs)) ->
                                  let uu____3341 = traverse f pol e a in
                                  (match uu____3341 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____3221 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____3445 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____3445 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____3459 =
                       let uu____3474 =
                         FStar_List.map
                           (fun uu____3507  ->
                              match uu____3507 with
                              | (bv,aq) ->
                                  let uu____3524 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____3524 with
                                   | (s',gs) ->
                                       (((let uu___172_3554 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___172_3554.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___172_3554.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____3474 in
                     (match uu____3459 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____3618 = traverse f pol e' topen in
                          (match uu____3618 with
                           | (topen',gs2) ->
                               let uu____3637 =
                                 let uu____3638 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____3638.FStar_Syntax_Syntax.n in
                               (uu____3637, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____3017 with
          | (tn',gs) ->
              let t' =
                let uu___173_3661 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___173_3661.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___173_3661.FStar_Syntax_Syntax.vars)
                } in
              let uu____3662 = f pol e t' in
              (match uu____3662 with
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
      (let uu____3721 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3721);
      (let uu____3769 = FStar_ST.op_Bang tacdbg in
       if uu____3769
       then
         let uu____3816 =
           let uu____3817 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____3817
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____3818 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3816
           uu____3818
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____3847 = traverse by_tactic_interp Pos env goal in
       match uu____3847 with
       | (t',gs) ->
           ((let uu____3869 = FStar_ST.op_Bang tacdbg in
             if uu____3869
             then
               let uu____3916 =
                 let uu____3917 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____3917
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____3918 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____3916 uu____3918
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____3965  ->
                    fun g  ->
                      match uu____3965 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4010 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4010 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4013 =
                                  let uu____4014 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4014 in
                                failwith uu____4013
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4017 = FStar_ST.op_Bang tacdbg in
                            if uu____4017
                            then
                              let uu____4064 = FStar_Util.string_of_int n1 in
                              let uu____4065 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4064 uu____4065
                            else ());
                           (let gt' =
                              let uu____4068 =
                                let uu____4069 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4069 in
                              FStar_TypeChecker_Util.label uu____4068
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4084 = s1 in
             match uu____4084 with
             | (uu____4105,gs1) ->
                 let uu____4123 =
                   let uu____4130 = FStar_Options.peek () in
                   (env, t', uu____4130) in
                 uu____4123 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4142 =
        let uu____4143 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4143 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4142 [FStar_Syntax_Syntax.U_zero] in
    let uu____4144 =
      let uu____4145 =
        let uu____4146 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4147 =
          let uu____4150 = FStar_Syntax_Syntax.as_arg a in [uu____4150] in
        uu____4146 :: uu____4147 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4145 in
    uu____4144 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4166 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4166);
        (let uu____4213 =
           let uu____4220 = reify_tactic tau in
           run_tactic_on_typ uu____4220 env typ in
         match uu____4213 with
         | (gs,w) ->
             let uu____4227 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4231 =
                      let uu____4232 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4232 in
                    Prims.op_Negation uu____4231) gs in
             if uu____4227
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)