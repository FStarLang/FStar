open Prims
let tacdbg: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let mk_tactic_interpretation_0:
  'r .
    'r FStar_Tactics_Basic.tac ->
      'r FStar_Syntax_Embeddings.embedder ->
        FStar_Syntax_Syntax.typ ->
          FStar_Ident.lid ->
            FStar_TypeChecker_Normalize.psc ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun embed_r  ->
      fun t_r  ->
        fun nm  ->
          fun psc  ->
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
                          let uu____102 =
                            FStar_TypeChecker_Normalize.psc_range psc in
                          FStar_Tactics_Embedding.embed_result embed_r t_r
                            uu____102 res in
                        FStar_Pervasives_Native.Some uu____101))
              | uu____109 ->
                  failwith "Unexpected application of tactic primitive"
let mk_tactic_interpretation_1:
  'a 'r .
    ('a -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'r FStar_Syntax_Embeddings.embedder ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (a,uu____190)::(embedded_state,uu____192)::[] ->
                    let uu____219 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____219
                      (fun ps  ->
                         FStar_Tactics_Basic.log ps
                           (fun uu____230  ->
                              let uu____231 = FStar_Ident.string_of_lid nm in
                              let uu____232 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____231 uu____232);
                         (let uu____233 = unembed_a a in
                          FStar_Util.bind_opt uu____233
                            (fun a1  ->
                               let res =
                                 let uu____245 = t a1 in
                                 FStar_Tactics_Basic.run uu____245 ps in
                               let uu____248 =
                                 let uu____249 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____249 res in
                               FStar_Pervasives_Native.Some uu____248)))
                | uu____256 ->
                    let uu____257 =
                      let uu____258 = FStar_Ident.string_of_lid nm in
                      let uu____259 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____258 uu____259 in
                    failwith uu____257
let mk_tactic_interpretation_1_env:
  'a 'r .
    (FStar_TypeChecker_Normalize.psc -> 'a -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'r FStar_Syntax_Embeddings.embedder ->
          FStar_Syntax_Syntax.typ ->
            FStar_Ident.lid ->
              FStar_TypeChecker_Normalize.psc ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun embed_r  ->
        fun t_r  ->
          fun nm  ->
            fun psc  ->
              fun args  ->
                match args with
                | (a,uu____345)::(embedded_state,uu____347)::[] ->
                    let uu____374 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____374
                      (fun ps  ->
                         FStar_Tactics_Basic.log ps
                           (fun uu____385  ->
                              let uu____386 = FStar_Ident.string_of_lid nm in
                              let uu____387 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____386 uu____387);
                         (let uu____388 = unembed_a a in
                          FStar_Util.bind_opt uu____388
                            (fun a1  ->
                               let res =
                                 let uu____400 = t psc a1 in
                                 FStar_Tactics_Basic.run uu____400 ps in
                               let uu____403 =
                                 let uu____404 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____404 res in
                               FStar_Pervasives_Native.Some uu____403)))
                | uu____411 ->
                    let uu____412 =
                      let uu____413 = FStar_Ident.string_of_lid nm in
                      let uu____414 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____413 uu____414 in
                    failwith uu____412
let mk_tactic_interpretation_2:
  'a 'b 'r .
    ('a -> 'b -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'b FStar_Syntax_Embeddings.unembedder ->
          'r FStar_Syntax_Embeddings.embedder ->
            FStar_Syntax_Syntax.typ ->
              FStar_Ident.lid ->
                FStar_TypeChecker_Normalize.psc ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun t  ->
    fun unembed_a  ->
      fun unembed_b  ->
        fun embed_r  ->
          fun t_r  ->
            fun nm  ->
              fun psc  ->
                fun args  ->
                  match args with
                  | (a,uu____517)::(b,uu____519)::(embedded_state,uu____521)::[]
                      ->
                      let uu____558 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      FStar_Util.bind_opt uu____558
                        (fun ps  ->
                           FStar_Tactics_Basic.log ps
                             (fun uu____569  ->
                                let uu____570 = FStar_Ident.string_of_lid nm in
                                let uu____571 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____570
                                  uu____571);
                           (let uu____572 = unembed_a a in
                            FStar_Util.bind_opt uu____572
                              (fun a1  ->
                                 let uu____580 = unembed_b b in
                                 FStar_Util.bind_opt uu____580
                                   (fun b1  ->
                                      let res =
                                        let uu____592 = t a1 b1 in
                                        FStar_Tactics_Basic.run uu____592 ps in
                                      let uu____595 =
                                        let uu____596 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc in
                                        FStar_Tactics_Embedding.embed_result
                                          embed_r t_r uu____596 res in
                                      FStar_Pervasives_Native.Some uu____595))))
                  | uu____603 ->
                      let uu____604 =
                        let uu____605 = FStar_Ident.string_of_lid nm in
                        let uu____606 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____605 uu____606 in
                      failwith uu____604
let mk_tactic_interpretation_3:
  'a 'b 'c 'r .
    ('a -> 'b -> 'c -> 'r FStar_Tactics_Basic.tac) ->
      'a FStar_Syntax_Embeddings.unembedder ->
        'b FStar_Syntax_Embeddings.unembedder ->
          'c FStar_Syntax_Embeddings.unembedder ->
            'r FStar_Syntax_Embeddings.embedder ->
              FStar_Syntax_Syntax.typ ->
                FStar_Ident.lid ->
                  FStar_TypeChecker_Normalize.psc ->
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
                fun psc  ->
                  fun args  ->
                    match args with
                    | (a,uu____731)::(b,uu____733)::(c,uu____735)::(embedded_state,uu____737)::[]
                        ->
                        let uu____784 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        FStar_Util.bind_opt uu____784
                          (fun ps  ->
                             FStar_Tactics_Basic.log ps
                               (fun uu____795  ->
                                  let uu____796 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____797 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____796
                                    uu____797);
                             (let uu____798 = unembed_a a in
                              FStar_Util.bind_opt uu____798
                                (fun a1  ->
                                   let uu____806 = unembed_b b in
                                   FStar_Util.bind_opt uu____806
                                     (fun b1  ->
                                        let uu____814 = unembed_c c in
                                        FStar_Util.bind_opt uu____814
                                          (fun c1  ->
                                             let res =
                                               let uu____826 = t a1 b1 c1 in
                                               FStar_Tactics_Basic.run
                                                 uu____826 ps in
                                             let uu____829 =
                                               let uu____830 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc in
                                               FStar_Tactics_Embedding.embed_result
                                                 embed_r t_r uu____830 res in
                                             FStar_Pervasives_Native.Some
                                               uu____829)))))
                    | uu____837 ->
                        let uu____838 =
                          let uu____839 = FStar_Ident.string_of_lid nm in
                          let uu____840 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____839 uu____840 in
                        failwith uu____838
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
                      FStar_TypeChecker_Normalize.psc ->
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
                    fun psc  ->
                      fun args  ->
                        match args with
                        | (a,uu____1009)::(b,uu____1011)::(c,uu____1013)::
                            (d,uu____1015)::(e,uu____1017)::(embedded_state,uu____1019)::[]
                            ->
                            let uu____1086 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state in
                            FStar_Util.bind_opt uu____1086
                              (fun ps  ->
                                 FStar_Tactics_Basic.log ps
                                   (fun uu____1097  ->
                                      let uu____1098 =
                                        FStar_Ident.string_of_lid nm in
                                      let uu____1099 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1098 uu____1099);
                                 (let uu____1100 = unembed_a a in
                                  FStar_Util.bind_opt uu____1100
                                    (fun a1  ->
                                       let uu____1108 = unembed_b b in
                                       FStar_Util.bind_opt uu____1108
                                         (fun b1  ->
                                            let uu____1116 = unembed_c c in
                                            FStar_Util.bind_opt uu____1116
                                              (fun c1  ->
                                                 let uu____1124 = unembed_d d in
                                                 FStar_Util.bind_opt
                                                   uu____1124
                                                   (fun d1  ->
                                                      let uu____1132 =
                                                        unembed_e e in
                                                      FStar_Util.bind_opt
                                                        uu____1132
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1144 =
                                                               t a1 b1 c1 d1
                                                                 e1 in
                                                             FStar_Tactics_Basic.run
                                                               uu____1144 ps in
                                                           let uu____1147 =
                                                             let uu____1148 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc in
                                                             FStar_Tactics_Embedding.embed_result
                                                               embed_r t_r
                                                               uu____1148 res in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1147)))))))
                        | uu____1155 ->
                            let uu____1156 =
                              let uu____1157 = FStar_Ident.string_of_lid nm in
                              let uu____1158 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1157 uu____1158 in
                            failwith uu____1156
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
  fun uu____1211  ->
    let mk1 nm arity interpretation =
      let nm1 = FStar_Tactics_Embedding.fstar_tactics_lid' ["Builtins"; nm] in
      {
        FStar_TypeChecker_Normalize.name = nm1;
        FStar_TypeChecker_Normalize.arity = arity;
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          (fun psc  -> fun args  -> interpretation nm1 psc args)
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
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____1851)::[] ->
          let uu____1868 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1868
            (fun ps1  ->
               let uu____1874 =
                 let uu____1875 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1876 = FStar_Tactics_Types.decr_depth ps1 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1875
                   uu____1876 in
               FStar_Pervasives_Native.Some uu____1874)
      | uu____1877 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1881 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1881;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1894)::[] ->
          let uu____1911 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1911
            (fun ps1  ->
               let uu____1917 =
                 let uu____1918 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1919 = FStar_Tactics_Types.incr_depth ps1 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1918
                   uu____1919 in
               FStar_Pervasives_Native.Some uu____1917)
      | uu____1920 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1924 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1924;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1941)::[] ->
          let uu____1958 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1958
            (fun ps1  ->
               FStar_Tactics_Types.tracepoint ps1;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1969 -> failwith "Unexpected application of tracepoint" in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let put1 rng t =
      let uu___172_1983 = t in
      {
        FStar_Syntax_Syntax.n = (uu___172_1983.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___172_1983.FStar_Syntax_Syntax.vars)
      } in
    let get1 t = FStar_Pervasives_Native.Some t in
    let uu____1990 =
      let uu____1993 =
        mktac0 "__trivial" FStar_Tactics_Basic.trivial
          FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
      let uu____1994 =
        let uu____1997 =
          let uu____1998 =
            FStar_Syntax_Embeddings.embed_option put1
              FStar_Syntax_Syntax.t_unit in
          mktac2 "__trytac" (fun uu____2008  -> FStar_Tactics_Basic.trytac)
            get1 (unembed_tactic_0' get1) uu____1998
            FStar_Syntax_Syntax.t_unit in
        let uu____2015 =
          let uu____2018 =
            mktac0 "__intro" FStar_Tactics_Basic.intro
              FStar_Reflection_Basic.embed_binder
              FStar_Reflection_Data.fstar_refl_binder in
          let uu____2019 =
            let uu____2022 =
              let uu____2023 =
                FStar_Syntax_Embeddings.embed_pair
                  FStar_Reflection_Basic.embed_binder
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Basic.embed_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              let uu____2030 =
                FStar_Tactics_Embedding.pair_typ
                  FStar_Reflection_Data.fstar_refl_binder
                  FStar_Reflection_Data.fstar_refl_binder in
              mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec uu____2023
                uu____2030 in
            let uu____2041 =
              let uu____2044 =
                let uu____2045 =
                  FStar_Syntax_Embeddings.unembed_list
                    FStar_Syntax_Embeddings.unembed_norm_step in
                mktac1 "__norm" FStar_Tactics_Basic.norm uu____2045
                  FStar_Syntax_Embeddings.embed_unit
                  FStar_Syntax_Syntax.t_unit in
              let uu____2056 =
                let uu____2059 =
                  let uu____2060 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step in
                  mktac3 "__norm_term_env" FStar_Tactics_Basic.norm_term_env
                    FStar_Reflection_Basic.unembed_env uu____2060
                    FStar_Reflection_Basic.unembed_term
                    FStar_Reflection_Basic.embed_term
                    FStar_Syntax_Syntax.t_term in
                let uu____2071 =
                  let uu____2074 =
                    mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                      FStar_Reflection_Basic.unembed_binder
                      FStar_Syntax_Embeddings.unembed_string
                      FStar_Syntax_Embeddings.embed_unit
                      FStar_Syntax_Syntax.t_unit in
                  let uu____2075 =
                    let uu____2078 =
                      mktac1 "__binder_retype"
                        FStar_Tactics_Basic.binder_retype
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____2079 =
                      let uu____2082 =
                        mktac0 "__revert" FStar_Tactics_Basic.revert
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____2083 =
                        let uu____2086 =
                          mktac0 "__clear_top" FStar_Tactics_Basic.clear_top
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____2087 =
                          let uu____2090 =
                            mktac1 "__clear" FStar_Tactics_Basic.clear
                              FStar_Reflection_Basic.unembed_binder
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____2091 =
                            let uu____2094 =
                              mktac1 "__rewrite" FStar_Tactics_Basic.rewrite
                                FStar_Reflection_Basic.unembed_binder
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____2095 =
                              let uu____2098 =
                                mktac0 "__smt" FStar_Tactics_Basic.smt
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____2099 =
                                let uu____2102 =
                                  mktac1 "__exact" FStar_Tactics_Basic.exact
                                    FStar_Reflection_Basic.unembed_term
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____2103 =
                                  let uu____2106 =
                                    mktac1 "__apply"
                                      (FStar_Tactics_Basic.apply true)
                                      FStar_Reflection_Basic.unembed_term
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____2107 =
                                    let uu____2110 =
                                      mktac1 "__apply_raw"
                                        (FStar_Tactics_Basic.apply false)
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____2111 =
                                      let uu____2114 =
                                        mktac1 "__apply_lemma"
                                          FStar_Tactics_Basic.apply_lemma
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____2115 =
                                        let uu____2118 =
                                          let uu____2119 =
                                            FStar_Syntax_Embeddings.embed_pair
                                              put1 FStar_Syntax_Syntax.t_unit
                                              put1 FStar_Syntax_Syntax.t_unit in
                                          mktac5 "__divide"
                                            (fun uu____2136  ->
                                               fun uu____2137  ->
                                                 FStar_Tactics_Basic.divide)
                                            get1 get1
                                            FStar_Syntax_Embeddings.unembed_int
                                            (unembed_tactic_0' get1)
                                            (unembed_tactic_0' get1)
                                            uu____2119
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____2144 =
                                          let uu____2147 =
                                            mktac1 "__set_options"
                                              FStar_Tactics_Basic.set_options
                                              FStar_Syntax_Embeddings.unembed_string
                                              FStar_Syntax_Embeddings.embed_unit
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____2148 =
                                            let uu____2151 =
                                              mktac2 "__seq"
                                                FStar_Tactics_Basic.seq
                                                (unembed_tactic_0'
                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                (unembed_tactic_0'
                                                   FStar_Syntax_Embeddings.unembed_unit)
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____2156 =
                                              let uu____2159 =
                                                mktac1 "__tc"
                                                  FStar_Tactics_Basic.tc
                                                  FStar_Reflection_Basic.unembed_term
                                                  FStar_Reflection_Basic.embed_term
                                                  FStar_Syntax_Syntax.t_term in
                                              let uu____2160 =
                                                let uu____2163 =
                                                  mktac1 "__unshelve"
                                                    FStar_Tactics_Basic.unshelve
                                                    FStar_Reflection_Basic.unembed_term
                                                    FStar_Syntax_Embeddings.embed_unit
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____2164 =
                                                  let uu____2167 =
                                                    mktac2 "__unquote"
                                                      FStar_Tactics_Basic.unquote
                                                      get1
                                                      FStar_Reflection_Basic.unembed_term
                                                      put1
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____2168 =
                                                    let uu____2171 =
                                                      mktac1 "__prune"
                                                        FStar_Tactics_Basic.prune
                                                        FStar_Syntax_Embeddings.unembed_string
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____2172 =
                                                      let uu____2175 =
                                                        mktac1 "__addns"
                                                          FStar_Tactics_Basic.addns
                                                          FStar_Syntax_Embeddings.unembed_string
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____2176 =
                                                        let uu____2179 =
                                                          mktac1 "__print"
                                                            (fun x  ->
                                                               FStar_Tactics_Basic.tacprint
                                                                 x;
                                                               FStar_Tactics_Basic.ret
                                                                 ())
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____2184 =
                                                          let uu____2187 =
                                                            mktac1_env
                                                              "__dump"
                                                              FStar_Tactics_Basic.print_proof_state
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____2188 =
                                                            let uu____2191 =
                                                              mktac1_env
                                                                "__dump1"
                                                                FStar_Tactics_Basic.print_proof_state1
                                                                FStar_Syntax_Embeddings.unembed_string
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____2192 =
                                                              let uu____2195
                                                                =
                                                                mktac2
                                                                  "__pointwise"
                                                                  FStar_Tactics_Basic.pointwise
                                                                  FStar_Tactics_Embedding.unembed_direction
                                                                  (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____2198
                                                                =
                                                                let uu____2201
                                                                  =
                                                                  mktac0
                                                                    "__trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____2202
                                                                  =
                                                                  let uu____2205
                                                                    =
                                                                    mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____2206
                                                                    =
                                                                    let uu____2209
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2210
                                                                    =
                                                                    let uu____2213
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2214
                                                                    =
                                                                    let uu____2217
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2218
                                                                    =
                                                                    let uu____2221
                                                                    =
                                                                    let uu____2222
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2229
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    uu____2222
                                                                    uu____2229 in
                                                                    let uu____2240
                                                                    =
                                                                    let uu____2243
                                                                    =
                                                                    mktac0
                                                                    "__top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2244
                                                                    =
                                                                    let uu____2247
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2248
                                                                    =
                                                                    let uu____2251
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2252
                                                                    =
                                                                    let uu____2255
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2256
                                                                    =
                                                                    let uu____2259
                                                                    =
                                                                    let uu____2260
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term in
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    uu____2260
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2271
                                                                    =
                                                                    let uu____2274
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2275
                                                                    =
                                                                    let uu____2278
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____2278;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step] in
                                                                    uu____2274
                                                                    ::
                                                                    uu____2275 in
                                                                    uu____2259
                                                                    ::
                                                                    uu____2271 in
                                                                    uu____2255
                                                                    ::
                                                                    uu____2256 in
                                                                    uu____2251
                                                                    ::
                                                                    uu____2252 in
                                                                    uu____2247
                                                                    ::
                                                                    uu____2248 in
                                                                    uu____2243
                                                                    ::
                                                                    uu____2244 in
                                                                    uu____2221
                                                                    ::
                                                                    uu____2240 in
                                                                    uu____2217
                                                                    ::
                                                                    uu____2218 in
                                                                    uu____2213
                                                                    ::
                                                                    uu____2214 in
                                                                    uu____2209
                                                                    ::
                                                                    uu____2210 in
                                                                  uu____2205
                                                                    ::
                                                                    uu____2206 in
                                                                uu____2201 ::
                                                                  uu____2202 in
                                                              uu____2195 ::
                                                                uu____2198 in
                                                            uu____2191 ::
                                                              uu____2192 in
                                                          uu____2187 ::
                                                            uu____2188 in
                                                        uu____2179 ::
                                                          uu____2184 in
                                                      uu____2175 ::
                                                        uu____2176 in
                                                    uu____2171 :: uu____2172 in
                                                  uu____2167 :: uu____2168 in
                                                uu____2163 :: uu____2164 in
                                              uu____2159 :: uu____2160 in
                                            uu____2151 :: uu____2156 in
                                          uu____2147 :: uu____2148 in
                                        uu____2118 :: uu____2144 in
                                      uu____2114 :: uu____2115 in
                                    uu____2110 :: uu____2111 in
                                  uu____2106 :: uu____2107 in
                                uu____2102 :: uu____2103 in
                              uu____2098 :: uu____2099 in
                            uu____2094 :: uu____2095 in
                          uu____2090 :: uu____2091 in
                        uu____2086 :: uu____2087 in
                      uu____2082 :: uu____2083 in
                    uu____2078 :: uu____2079 in
                  uu____2074 :: uu____2075 in
                uu____2059 :: uu____2071 in
              uu____2044 :: uu____2056 in
            uu____2022 :: uu____2041 in
          uu____2018 :: uu____2019 in
        uu____1997 :: uu____2015 in
      uu____1993 :: uu____1994 in
    FStar_List.append uu____1990
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
             let uu____2301 =
               let uu____2302 =
                 let uu____2303 =
                   let uu____2304 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____2304 in
                 [uu____2303] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2302 in
             uu____2301 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2311 = FStar_ST.op_Bang tacdbg in
            if uu____2311
            then
              let uu____2358 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2358
            else ());
           (let result =
              let uu____2361 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2361 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2365 = FStar_ST.op_Bang tacdbg in
             if uu____2365
             then
               let uu____2412 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2412
             else ());
            (let uu____2414 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2414 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2457 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2457
                   (fun uu____2461  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2484 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2484
                   (fun uu____2488  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2501 =
                   let uu____2502 =
                     let uu____2507 =
                       let uu____2508 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____2508 in
                     (uu____2507,
                       ((proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)) in
                   FStar_Errors.Error uu____2502 in
                 FStar_Exn.raise uu____2501)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2517 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
        uu____2517
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2571  ->
             match uu____2571 with
             | (r,uu____2589,uv,uu____2591,ty,rng) ->
                 let uu____2594 =
                   let uu____2595 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2596 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2595 uu____2596 r in
                 (uu____2594, rng)) is in
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
        (let uu____2644 = FStar_ST.op_Bang tacdbg in
         if uu____2644
         then
           let uu____2691 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2691
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         (let uu____2695 = FStar_ST.op_Bang tacdbg in
          if uu____2695
          then
            let uu____2742 = FStar_Syntax_Print.term_to_string tactic1 in
            FStar_Util.print1 "About to check tactic term: %s\n" uu____2742
          else ());
         (let uu____2744 =
            FStar_TypeChecker_TcTerm.tc_reified_tactic env tactic1 in
          match uu____2744 with
          | (tactic2,uu____2758,g) ->
              (FStar_TypeChecker_Rel.force_trivial_guard env g;
               FStar_Errors.stop_if_err ();
               (let tau =
                  unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit
                    tactic2 in
                let uu____2765 = FStar_TypeChecker_Env.clear_expected_typ env in
                match uu____2765 with
                | (env1,uu____2779) ->
                    let env2 =
                      let uu___173_2785 = env1 in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___173_2785.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___173_2785.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___173_2785.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___173_2785.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___173_2785.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___173_2785.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___173_2785.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___173_2785.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___173_2785.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp = false;
                        FStar_TypeChecker_Env.effects =
                          (uu___173_2785.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___173_2785.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___173_2785.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___173_2785.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___173_2785.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___173_2785.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___173_2785.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___173_2785.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___173_2785.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___173_2785.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.failhard =
                          (uu___173_2785.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___173_2785.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___173_2785.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___173_2785.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___173_2785.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___173_2785.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qname_and_index =
                          (uu___173_2785.FStar_TypeChecker_Env.qname_and_index);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___173_2785.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth =
                          (uu___173_2785.FStar_TypeChecker_Env.synth);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___173_2785.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___173_2785.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___173_2785.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___173_2785.FStar_TypeChecker_Env.dsenv)
                      } in
                    let uu____2786 =
                      FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
                    (match uu____2786 with
                     | (ps,w) ->
                         ((let uu____2800 = FStar_ST.op_Bang tacdbg in
                           if uu____2800
                           then
                             let uu____2847 =
                               FStar_Syntax_Print.term_to_string typ in
                             FStar_Util.print1
                               "Running tactic with goal = %s\n" uu____2847
                           else ());
                          (let uu____2849 = FStar_Tactics_Basic.run tau ps in
                           match uu____2849 with
                           | FStar_Tactics_Result.Success (uu____2858,ps1) ->
                               ((let uu____2861 = FStar_ST.op_Bang tacdbg in
                                 if uu____2861
                                 then
                                   let uu____2908 =
                                     FStar_Syntax_Print.term_to_string w in
                                   FStar_Util.print1
                                     "Tactic generated proofterm %s\n"
                                     uu____2908
                                 else ());
                                FStar_List.iter
                                  (fun g1  ->
                                     let uu____2915 =
                                       FStar_Tactics_Basic.is_irrelevant g1 in
                                     if uu____2915
                                     then
                                       let uu____2916 =
                                         FStar_TypeChecker_Rel.teq_nosmt
                                           g1.FStar_Tactics_Types.context
                                           g1.FStar_Tactics_Types.witness
                                           FStar_Syntax_Util.exp_unit in
                                       (if uu____2916
                                        then ()
                                        else
                                          (let uu____2918 =
                                             let uu____2919 =
                                               FStar_Syntax_Print.term_to_string
                                                 g1.FStar_Tactics_Types.witness in
                                             FStar_Util.format1
                                               "Irrelevant tactic witness does not unify with (): %s"
                                               uu____2919 in
                                           failwith uu____2918))
                                     else ())
                                  (FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals);
                                (let g1 =
                                   let uu___174_2922 =
                                     FStar_TypeChecker_Rel.trivial_guard in
                                   {
                                     FStar_TypeChecker_Env.guard_f =
                                       (uu___174_2922.FStar_TypeChecker_Env.guard_f);
                                     FStar_TypeChecker_Env.deferred =
                                       (uu___174_2922.FStar_TypeChecker_Env.deferred);
                                     FStar_TypeChecker_Env.univ_ineqs =
                                       (uu___174_2922.FStar_TypeChecker_Env.univ_ineqs);
                                     FStar_TypeChecker_Env.implicits =
                                       (ps1.FStar_Tactics_Types.all_implicits)
                                   } in
                                 let g2 =
                                   let uu____2924 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env2 g1 in
                                   FStar_All.pipe_right uu____2924
                                     FStar_TypeChecker_Rel.resolve_implicits_tac in
                                 report_implicits ps1
                                   g2.FStar_TypeChecker_Env.implicits;
                                 ((FStar_List.append
                                     ps1.FStar_Tactics_Types.goals
                                     ps1.FStar_Tactics_Types.smt_goals), w)))
                           | FStar_Tactics_Result.Failed (s,ps1) ->
                               (FStar_Tactics_Basic.dump_proofstate ps1
                                  "at the time of failure";
                                (let uu____2931 =
                                   let uu____2932 =
                                     let uu____2937 =
                                       FStar_Util.format1
                                         "user tactic failed: %s" s in
                                     (uu____2937,
                                       (typ.FStar_Syntax_Syntax.pos)) in
                                   FStar_Errors.Error uu____2932 in
                                 FStar_Exn.raise uu____2931)))))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2948 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2953 -> false
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
        let uu____2982 = FStar_Syntax_Util.head_and_args t in
        match uu____2982 with
        | (hd1,args) ->
            let uu____3025 =
              let uu____3038 =
                let uu____3039 = FStar_Syntax_Util.un_uinst hd1 in
                uu____3039.FStar_Syntax_Syntax.n in
              (uu____3038, args) in
            (match uu____3025 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3058))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____3127 = run_tactic_on_typ tactic e assertion in
                   (match uu____3127 with
                    | (gs,uu____3141) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____3193 =
                     let uu____3196 =
                       let uu____3197 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____3197 in
                     [uu____3196] in
                   (FStar_Syntax_Util.t_true, uu____3193)
                 else (assertion, [])
             | uu____3213 -> (t, []))
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
          let uu____3283 =
            let uu____3290 =
              let uu____3291 = FStar_Syntax_Subst.compress t in
              uu____3291.FStar_Syntax_Syntax.n in
            match uu____3290 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____3306 = traverse f pol e t1 in
                (match uu____3306 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____3333 = traverse f pol e t1 in
                (match uu____3333 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3355;
                   FStar_Syntax_Syntax.vars = uu____3356;_},(p,uu____3358)::
                 (q,uu____3360)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3400 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3400 in
                let uu____3401 = traverse f (flip pol) e p in
                (match uu____3401 with
                 | (p',gs1) ->
                     let uu____3420 =
                       let uu____3427 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____3427 q in
                     (match uu____3420 with
                      | (q',gs2) ->
                          let uu____3440 =
                            let uu____3441 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____3441.FStar_Syntax_Syntax.n in
                          (uu____3440, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____3468 = traverse f pol e hd1 in
                (match uu____3468 with
                 | (hd',gs1) ->
                     let uu____3487 =
                       FStar_List.fold_right
                         (fun uu____3525  ->
                            fun uu____3526  ->
                              match (uu____3525, uu____3526) with
                              | ((a,q),(as',gs)) ->
                                  let uu____3607 = traverse f pol e a in
                                  (match uu____3607 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____3487 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____3711 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____3711 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____3725 =
                       let uu____3740 =
                         FStar_List.map
                           (fun uu____3773  ->
                              match uu____3773 with
                              | (bv,aq) ->
                                  let uu____3790 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____3790 with
                                   | (s',gs) ->
                                       (((let uu___175_3820 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___175_3820.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___175_3820.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____3740 in
                     (match uu____3725 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____3884 = traverse f pol e' topen in
                          (match uu____3884 with
                           | (topen',gs2) ->
                               let uu____3903 =
                                 let uu____3904 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____3904.FStar_Syntax_Syntax.n in
                               (uu____3903, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____3283 with
          | (tn',gs) ->
              let t' =
                let uu___176_3927 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___176_3927.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___176_3927.FStar_Syntax_Syntax.vars)
                } in
              let uu____3928 = f pol e t' in
              (match uu____3928 with
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
          [FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
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
      (let uu____3987 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3987);
      (let uu____4035 = FStar_ST.op_Bang tacdbg in
       if uu____4035
       then
         let uu____4082 =
           let uu____4083 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____4083
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____4084 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4082
           uu____4084
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____4113 = traverse by_tactic_interp Pos env goal in
       match uu____4113 with
       | (t',gs) ->
           ((let uu____4135 = FStar_ST.op_Bang tacdbg in
             if uu____4135
             then
               let uu____4182 =
                 let uu____4183 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4183
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4184 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4182 uu____4184
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4231  ->
                    fun g  ->
                      match uu____4231 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4276 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4276 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4279 =
                                  let uu____4280 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4280 in
                                failwith uu____4279
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4283 = FStar_ST.op_Bang tacdbg in
                            if uu____4283
                            then
                              let uu____4330 = FStar_Util.string_of_int n1 in
                              let uu____4331 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4330 uu____4331
                            else ());
                           (let gt' =
                              let uu____4334 =
                                let uu____4335 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4335 in
                              FStar_TypeChecker_Util.label uu____4334
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4350 = s1 in
             match uu____4350 with
             | (uu____4371,gs1) ->
                 let uu____4389 =
                   let uu____4396 = FStar_Options.peek () in
                   (env, t', uu____4396) in
                 uu____4389 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4408 =
        let uu____4409 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4409 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4408 [FStar_Syntax_Syntax.U_zero] in
    let uu____4410 =
      let uu____4411 =
        let uu____4412 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4413 =
          let uu____4416 = FStar_Syntax_Syntax.as_arg a in [uu____4416] in
        uu____4412 :: uu____4413 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4411 in
    uu____4410 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4432 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4432);
        (let uu____4479 =
           let uu____4486 = reify_tactic tau in
           run_tactic_on_typ uu____4486 env typ in
         match uu____4479 with
         | (gs,w) ->
             let uu____4493 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4497 =
                      let uu____4498 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4498 in
                    Prims.op_Negation uu____4497) gs in
             if uu____4493
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)