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
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____97  ->
                            let uu____98 = FStar_Ident.string_of_lid nm in
                            let uu____99 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____98 uu____99);
                       (let res = FStar_Tactics_Basic.run t ps1 in
                        let uu____103 =
                          let uu____104 =
                            FStar_TypeChecker_Normalize.psc_range psc in
                          FStar_Tactics_Embedding.embed_result embed_r t_r
                            uu____104 res in
                        FStar_Pervasives_Native.Some uu____103))
              | uu____111 ->
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
                | (a,uu____192)::(embedded_state,uu____194)::[] ->
                    let uu____221 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____221
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____234  ->
                              let uu____235 = FStar_Ident.string_of_lid nm in
                              let uu____236 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____235 uu____236);
                         (let uu____237 = unembed_a a in
                          FStar_Util.bind_opt uu____237
                            (fun a1  ->
                               let res =
                                 let uu____249 = t a1 in
                                 FStar_Tactics_Basic.run uu____249 ps1 in
                               let uu____252 =
                                 let uu____253 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____253 res in
                               FStar_Pervasives_Native.Some uu____252)))
                | uu____260 ->
                    let uu____261 =
                      let uu____262 = FStar_Ident.string_of_lid nm in
                      let uu____263 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____262 uu____263 in
                    failwith uu____261
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
                | (a,uu____349)::(embedded_state,uu____351)::[] ->
                    let uu____378 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____378
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____391  ->
                              let uu____392 = FStar_Ident.string_of_lid nm in
                              let uu____393 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____392 uu____393);
                         (let uu____394 = unembed_a a in
                          FStar_Util.bind_opt uu____394
                            (fun a1  ->
                               let res =
                                 let uu____406 = t psc a1 in
                                 FStar_Tactics_Basic.run uu____406 ps1 in
                               let uu____409 =
                                 let uu____410 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____410 res in
                               FStar_Pervasives_Native.Some uu____409)))
                | uu____417 ->
                    let uu____418 =
                      let uu____419 = FStar_Ident.string_of_lid nm in
                      let uu____420 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____419 uu____420 in
                    failwith uu____418
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
                  | (a,uu____523)::(b,uu____525)::(embedded_state,uu____527)::[]
                      ->
                      let uu____564 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      FStar_Util.bind_opt uu____564
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____577  ->
                                let uu____578 = FStar_Ident.string_of_lid nm in
                                let uu____579 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____578
                                  uu____579);
                           (let uu____580 = unembed_a a in
                            FStar_Util.bind_opt uu____580
                              (fun a1  ->
                                 let uu____588 = unembed_b b in
                                 FStar_Util.bind_opt uu____588
                                   (fun b1  ->
                                      let res =
                                        let uu____600 = t a1 b1 in
                                        FStar_Tactics_Basic.run uu____600 ps1 in
                                      let uu____603 =
                                        let uu____604 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc in
                                        FStar_Tactics_Embedding.embed_result
                                          embed_r t_r uu____604 res in
                                      FStar_Pervasives_Native.Some uu____603))))
                  | uu____611 ->
                      let uu____612 =
                        let uu____613 = FStar_Ident.string_of_lid nm in
                        let uu____614 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____613 uu____614 in
                      failwith uu____612
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
                    | (a,uu____739)::(b,uu____741)::(c,uu____743)::(embedded_state,uu____745)::[]
                        ->
                        let uu____792 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        FStar_Util.bind_opt uu____792
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____805  ->
                                  let uu____806 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____807 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____806
                                    uu____807);
                             (let uu____808 = unembed_a a in
                              FStar_Util.bind_opt uu____808
                                (fun a1  ->
                                   let uu____816 = unembed_b b in
                                   FStar_Util.bind_opt uu____816
                                     (fun b1  ->
                                        let uu____824 = unembed_c c in
                                        FStar_Util.bind_opt uu____824
                                          (fun c1  ->
                                             let res =
                                               let uu____836 = t a1 b1 c1 in
                                               FStar_Tactics_Basic.run
                                                 uu____836 ps1 in
                                             let uu____839 =
                                               let uu____840 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc in
                                               FStar_Tactics_Embedding.embed_result
                                                 embed_r t_r uu____840 res in
                                             FStar_Pervasives_Native.Some
                                               uu____839)))))
                    | uu____847 ->
                        let uu____848 =
                          let uu____849 = FStar_Ident.string_of_lid nm in
                          let uu____850 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____849 uu____850 in
                        failwith uu____848
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
                        | (a,uu____1019)::(b,uu____1021)::(c,uu____1023)::
                            (d,uu____1025)::(e,uu____1027)::(embedded_state,uu____1029)::[]
                            ->
                            let uu____1096 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state in
                            FStar_Util.bind_opt uu____1096
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1109  ->
                                      let uu____1110 =
                                        FStar_Ident.string_of_lid nm in
                                      let uu____1111 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1110 uu____1111);
                                 (let uu____1112 = unembed_a a in
                                  FStar_Util.bind_opt uu____1112
                                    (fun a1  ->
                                       let uu____1120 = unembed_b b in
                                       FStar_Util.bind_opt uu____1120
                                         (fun b1  ->
                                            let uu____1128 = unembed_c c in
                                            FStar_Util.bind_opt uu____1128
                                              (fun c1  ->
                                                 let uu____1136 = unembed_d d in
                                                 FStar_Util.bind_opt
                                                   uu____1136
                                                   (fun d1  ->
                                                      let uu____1144 =
                                                        unembed_e e in
                                                      FStar_Util.bind_opt
                                                        uu____1144
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1156 =
                                                               t a1 b1 c1 d1
                                                                 e1 in
                                                             FStar_Tactics_Basic.run
                                                               uu____1156 ps1 in
                                                           let uu____1159 =
                                                             let uu____1160 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc in
                                                             FStar_Tactics_Embedding.embed_result
                                                               embed_r t_r
                                                               uu____1160 res in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1159)))))))
                        | uu____1167 ->
                            let uu____1168 =
                              let uu____1169 = FStar_Ident.string_of_lid nm in
                              let uu____1170 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1169 uu____1170 in
                            failwith uu____1168
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
        (fun psc  -> fun args  -> s.FStar_Tactics_Native.tactic psc args)
    }
let rec primitive_steps:
  Prims.unit -> FStar_TypeChecker_Normalize.primitive_step Prims.list =
  fun uu____1223  ->
    let mk1 nm arity interpretation =
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
      | (ps,uu____1757)::[] ->
          let uu____1774 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1774
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1782 =
                 let uu____1783 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1784 = FStar_Tactics_Types.decr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1783
                   uu____1784 in
               FStar_Pervasives_Native.Some uu____1782)
      | uu____1785 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1789 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1789;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1802)::[] ->
          let uu____1819 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1819
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1827 =
                 let uu____1828 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1829 = FStar_Tactics_Types.incr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1828
                   uu____1829 in
               FStar_Pervasives_Native.Some uu____1827)
      | uu____1830 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1834 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1834;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1851)::[] ->
          let uu____1868 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1868
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1881 -> failwith "Unexpected application of tracepoint" in
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
      let uu___183_1895 = t in
      {
        FStar_Syntax_Syntax.n = (uu___183_1895.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___183_1895.FStar_Syntax_Syntax.vars)
      } in
    let get1 t = FStar_Pervasives_Native.Some t in
    let uu____1902 =
      let uu____1905 =
        mktac2 "__fail" (fun uu____1907  -> FStar_Tactics_Basic.fail) get1
          FStar_Syntax_Embeddings.unembed_string put1
          FStar_Syntax_Syntax.t_unit in
      let uu____1908 =
        let uu____1911 =
          mktac0 "__trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
        let uu____1912 =
          let uu____1915 =
            let uu____1916 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit in
            mktac2 "__trytac" (fun uu____1926  -> FStar_Tactics_Basic.trytac)
              get1 (unembed_tactic_0' get1) uu____1916
              FStar_Syntax_Syntax.t_unit in
          let uu____1933 =
            let uu____1936 =
              mktac0 "__intro" FStar_Tactics_Basic.intro
                FStar_Reflection_Basic.embed_binder
                FStar_Reflection_Data.fstar_refl_binder in
            let uu____1937 =
              let uu____1940 =
                let uu____1941 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                let uu____1948 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec uu____1941
                  uu____1948 in
              let uu____1959 =
                let uu____1962 =
                  let uu____1963 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step in
                  mktac1 "__norm" FStar_Tactics_Basic.norm uu____1963
                    FStar_Syntax_Embeddings.embed_unit
                    FStar_Syntax_Syntax.t_unit in
                let uu____1974 =
                  let uu____1977 =
                    let uu____1978 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step in
                    mktac3 "__norm_term_env"
                      FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Basic.unembed_env uu____1978
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_term
                      FStar_Syntax_Syntax.t_term in
                  let uu____1989 =
                    let uu____1992 =
                      let uu____1993 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step in
                      mktac2 "__norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____1993
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____2004 =
                      let uu____2007 =
                        mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Basic.unembed_binder
                          FStar_Syntax_Embeddings.unembed_string
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____2008 =
                        let uu____2011 =
                          mktac1 "__binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Basic.unembed_binder
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____2012 =
                          let uu____2015 =
                            mktac0 "__revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____2016 =
                            let uu____2019 =
                              mktac0 "__clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____2020 =
                              let uu____2023 =
                                mktac1 "__clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Basic.unembed_binder
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____2024 =
                                let uu____2027 =
                                  mktac1 "__rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Basic.unembed_binder
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____2028 =
                                  let uu____2031 =
                                    mktac0 "__smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____2032 =
                                    let uu____2035 =
                                      mktac1 "__exact"
                                        FStar_Tactics_Basic.exact
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____2036 =
                                      let uu____2039 =
                                        mktac1 "__apply"
                                          (FStar_Tactics_Basic.apply true)
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____2040 =
                                        let uu____2043 =
                                          mktac1 "__apply_raw"
                                            (FStar_Tactics_Basic.apply false)
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____2044 =
                                          let uu____2047 =
                                            mktac1 "__apply_lemma"
                                              FStar_Tactics_Basic.apply_lemma
                                              FStar_Reflection_Basic.unembed_term
                                              FStar_Syntax_Embeddings.embed_unit
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____2048 =
                                            let uu____2051 =
                                              let uu____2052 =
                                                FStar_Syntax_Embeddings.embed_pair
                                                  put1
                                                  FStar_Syntax_Syntax.t_unit
                                                  put1
                                                  FStar_Syntax_Syntax.t_unit in
                                              mktac5 "__divide"
                                                (fun uu____2069  ->
                                                   fun uu____2070  ->
                                                     FStar_Tactics_Basic.divide)
                                                get1 get1
                                                FStar_Syntax_Embeddings.unembed_int
                                                (unembed_tactic_0' get1)
                                                (unembed_tactic_0' get1)
                                                uu____2052
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____2077 =
                                              let uu____2080 =
                                                mktac1 "__set_options"
                                                  FStar_Tactics_Basic.set_options
                                                  FStar_Syntax_Embeddings.unembed_string
                                                  FStar_Syntax_Embeddings.embed_unit
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____2081 =
                                                let uu____2084 =
                                                  mktac2 "__seq"
                                                    FStar_Tactics_Basic.seq
                                                    (unembed_tactic_0'
                                                       FStar_Syntax_Embeddings.unembed_unit)
                                                    (unembed_tactic_0'
                                                       FStar_Syntax_Embeddings.unembed_unit)
                                                    FStar_Syntax_Embeddings.embed_unit
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____2089 =
                                                  let uu____2092 =
                                                    mktac1 "__tc"
                                                      FStar_Tactics_Basic.tc
                                                      FStar_Reflection_Basic.unembed_term
                                                      FStar_Reflection_Basic.embed_term
                                                      FStar_Syntax_Syntax.t_term in
                                                  let uu____2093 =
                                                    let uu____2096 =
                                                      mktac1 "__unshelve"
                                                        FStar_Tactics_Basic.unshelve
                                                        FStar_Reflection_Basic.unembed_term
                                                        FStar_Syntax_Embeddings.embed_unit
                                                        FStar_Syntax_Syntax.t_unit in
                                                    let uu____2097 =
                                                      let uu____2100 =
                                                        mktac2 "__unquote"
                                                          FStar_Tactics_Basic.unquote
                                                          get1
                                                          FStar_Reflection_Basic.unembed_term
                                                          put1
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____2101 =
                                                        let uu____2104 =
                                                          mktac1 "__prune"
                                                            FStar_Tactics_Basic.prune
                                                            FStar_Syntax_Embeddings.unembed_string
                                                            FStar_Syntax_Embeddings.embed_unit
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____2105 =
                                                          let uu____2108 =
                                                            mktac1 "__addns"
                                                              FStar_Tactics_Basic.addns
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____2109 =
                                                            let uu____2112 =
                                                              mktac1
                                                                "__print"
                                                                (fun x  ->
                                                                   FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                   FStar_Tactics_Basic.ret
                                                                    ())
                                                                FStar_Syntax_Embeddings.unembed_string
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____2117 =
                                                              let uu____2120
                                                                =
                                                                mktac1
                                                                  "__dump"
                                                                  FStar_Tactics_Basic.print_proof_state
                                                                  FStar_Syntax_Embeddings.unembed_string
                                                                  FStar_Syntax_Embeddings.embed_unit
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____2121
                                                                =
                                                                let uu____2124
                                                                  =
                                                                  mktac1
                                                                    "__dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____2125
                                                                  =
                                                                  let uu____2128
                                                                    =
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.unembed_direction
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____2131
                                                                    =
                                                                    let uu____2134
                                                                    =
                                                                    mktac0
                                                                    "__trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2135
                                                                    =
                                                                    let uu____2138
                                                                    =
                                                                    mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2139
                                                                    =
                                                                    let uu____2142
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2143
                                                                    =
                                                                    let uu____2146
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2147
                                                                    =
                                                                    let uu____2150
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2151
                                                                    =
                                                                    let uu____2154
                                                                    =
                                                                    let uu____2155
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2162
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    uu____2155
                                                                    uu____2162 in
                                                                    let uu____2173
                                                                    =
                                                                    let uu____2176
                                                                    =
                                                                    mktac0
                                                                    "__top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2177
                                                                    =
                                                                    let uu____2180
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2181
                                                                    =
                                                                    let uu____2184
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2185
                                                                    =
                                                                    let uu____2188
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2189
                                                                    =
                                                                    let uu____2192
                                                                    =
                                                                    let uu____2193
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term in
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    uu____2193
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2204
                                                                    =
                                                                    let uu____2207
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2208
                                                                    =
                                                                    let uu____2211
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____2211;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step] in
                                                                    uu____2207
                                                                    ::
                                                                    uu____2208 in
                                                                    uu____2192
                                                                    ::
                                                                    uu____2204 in
                                                                    uu____2188
                                                                    ::
                                                                    uu____2189 in
                                                                    uu____2184
                                                                    ::
                                                                    uu____2185 in
                                                                    uu____2180
                                                                    ::
                                                                    uu____2181 in
                                                                    uu____2176
                                                                    ::
                                                                    uu____2177 in
                                                                    uu____2154
                                                                    ::
                                                                    uu____2173 in
                                                                    uu____2150
                                                                    ::
                                                                    uu____2151 in
                                                                    uu____2146
                                                                    ::
                                                                    uu____2147 in
                                                                    uu____2142
                                                                    ::
                                                                    uu____2143 in
                                                                    uu____2138
                                                                    ::
                                                                    uu____2139 in
                                                                    uu____2134
                                                                    ::
                                                                    uu____2135 in
                                                                  uu____2128
                                                                    ::
                                                                    uu____2131 in
                                                                uu____2124 ::
                                                                  uu____2125 in
                                                              uu____2120 ::
                                                                uu____2121 in
                                                            uu____2112 ::
                                                              uu____2117 in
                                                          uu____2108 ::
                                                            uu____2109 in
                                                        uu____2104 ::
                                                          uu____2105 in
                                                      uu____2100 ::
                                                        uu____2101 in
                                                    uu____2096 :: uu____2097 in
                                                  uu____2092 :: uu____2093 in
                                                uu____2084 :: uu____2089 in
                                              uu____2080 :: uu____2081 in
                                            uu____2051 :: uu____2077 in
                                          uu____2047 :: uu____2048 in
                                        uu____2043 :: uu____2044 in
                                      uu____2039 :: uu____2040 in
                                    uu____2035 :: uu____2036 in
                                  uu____2031 :: uu____2032 in
                                uu____2027 :: uu____2028 in
                              uu____2023 :: uu____2024 in
                            uu____2019 :: uu____2020 in
                          uu____2015 :: uu____2016 in
                        uu____2011 :: uu____2012 in
                      uu____2007 :: uu____2008 in
                    uu____1992 :: uu____2004 in
                  uu____1977 :: uu____1989 in
                uu____1962 :: uu____1974 in
              uu____1940 :: uu____1959 in
            uu____1936 :: uu____1937 in
          uu____1915 :: uu____1933 in
        uu____1911 :: uu____1912 in
      uu____1905 :: uu____1908 in
    FStar_List.append uu____1902
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
             let uu____2234 =
               let uu____2235 =
                 let uu____2236 =
                   let uu____2237 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____2237 in
                 [uu____2236] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2235 in
             uu____2234 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2244 = FStar_ST.op_Bang tacdbg in
            if uu____2244
            then
              let uu____2291 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2291
            else ());
           (let result =
              let uu____2294 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2294 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2298 = FStar_ST.op_Bang tacdbg in
             if uu____2298
             then
               let uu____2345 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2345
             else ());
            (let uu____2347 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2347 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2390 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2390
                   (fun uu____2394  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2417 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2417
                   (fun uu____2421  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2434 =
                   let uu____2435 =
                     let uu____2440 =
                       let uu____2441 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____2441 in
                     (uu____2440,
                       ((proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)) in
                   FStar_Errors.Error uu____2435 in
                 FStar_Exn.raise uu____2434)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2450 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_65  -> FStar_Pervasives_Native.Some _0_65)
        uu____2450
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2504  ->
             match uu____2504 with
             | (r,uu____2522,uv,uu____2524,ty,rng) ->
                 let uu____2527 =
                   let uu____2528 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2529 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2528 uu____2529 r in
                 (uu____2527, rng)) is in
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
        (let uu____2577 = FStar_ST.op_Bang tacdbg in
         if uu____2577
         then
           let uu____2624 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2624
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1 in
          let uu____2631 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____2631 with
          | (env1,uu____2645) ->
              let env2 =
                let uu___184_2651 = env1 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___184_2651.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___184_2651.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___184_2651.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___184_2651.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___184_2651.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___184_2651.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___184_2651.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___184_2651.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___184_2651.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___184_2651.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___184_2651.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___184_2651.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___184_2651.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___184_2651.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___184_2651.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___184_2651.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___184_2651.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___184_2651.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___184_2651.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___184_2651.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___184_2651.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___184_2651.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___184_2651.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___184_2651.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___184_2651.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___184_2651.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___184_2651.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___184_2651.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___184_2651.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___184_2651.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___184_2651.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___184_2651.FStar_TypeChecker_Env.dsenv)
                } in
              let uu____2652 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
              (match uu____2652 with
               | (ps,w) ->
                   ((let uu____2666 = FStar_ST.op_Bang tacdbg in
                     if uu____2666
                     then
                       let uu____2713 = FStar_Syntax_Print.term_to_string typ in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2713
                     else ());
                    (let uu____2715 = FStar_Tactics_Basic.run tau ps in
                     match uu____2715 with
                     | FStar_Tactics_Result.Success (uu____2724,ps1) ->
                         ((let uu____2727 = FStar_ST.op_Bang tacdbg in
                           if uu____2727
                           then
                             let uu____2774 =
                               FStar_Syntax_Print.term_to_string w in
                             FStar_Util.print1
                               "Tactic generated proofterm %s\n" uu____2774
                           else ());
                          FStar_List.iter
                            (fun g  ->
                               let uu____2781 =
                                 FStar_Tactics_Basic.is_irrelevant g in
                               if uu____2781
                               then
                                 let uu____2782 =
                                   FStar_TypeChecker_Rel.teq_nosmt
                                     g.FStar_Tactics_Types.context
                                     g.FStar_Tactics_Types.witness
                                     FStar_Syntax_Util.exp_unit in
                                 (if uu____2782
                                  then ()
                                  else
                                    (let uu____2784 =
                                       let uu____2785 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Types.witness in
                                       FStar_Util.format1
                                         "Irrelevant tactic witness does not unify with (): %s"
                                         uu____2785 in
                                     failwith uu____2784))
                               else ())
                            (FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals);
                          (let g =
                             let uu___185_2788 =
                               FStar_TypeChecker_Rel.trivial_guard in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___185_2788.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___185_2788.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (uu___185_2788.FStar_TypeChecker_Env.univ_ineqs);
                               FStar_TypeChecker_Env.implicits =
                                 (ps1.FStar_Tactics_Types.all_implicits)
                             } in
                           let g1 =
                             let uu____2790 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____2790
                               FStar_TypeChecker_Rel.resolve_implicits_tac in
                           report_implicits ps1
                             g1.FStar_TypeChecker_Env.implicits;
                           ((FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals), w)))
                     | FStar_Tactics_Result.Failed (s,ps1) ->
                         ((let uu____2797 =
                             let uu____2798 =
                               FStar_TypeChecker_Normalize.psc_subst
                                 ps1.FStar_Tactics_Types.psc in
                             FStar_Tactics_Types.subst_proof_state uu____2798
                               ps1 in
                           FStar_Tactics_Basic.dump_proofstate uu____2797
                             "at the time of failure");
                          (let uu____2799 =
                             let uu____2800 =
                               let uu____2805 =
                                 FStar_Util.format1 "user tactic failed: %s"
                                   s in
                               (uu____2805, (typ.FStar_Syntax_Syntax.pos)) in
                             FStar_Errors.Error uu____2800 in
                           FStar_Exn.raise uu____2799)))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2816 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2821 -> false
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
        let uu____2850 = FStar_Syntax_Util.head_and_args t in
        match uu____2850 with
        | (hd1,args) ->
            let uu____2893 =
              let uu____2906 =
                let uu____2907 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2907.FStar_Syntax_Syntax.n in
              (uu____2906, args) in
            (match uu____2893 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2926))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____2995 = run_tactic_on_typ tactic e assertion in
                   (match uu____2995 with
                    | (gs,uu____3009) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____3061 =
                     let uu____3064 =
                       let uu____3065 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____3065 in
                     [uu____3064] in
                   (FStar_Syntax_Util.t_true, uu____3061)
                 else (assertion, [])
             | uu____3081 -> (t, []))
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
          let uu____3151 =
            let uu____3158 =
              let uu____3159 = FStar_Syntax_Subst.compress t in
              uu____3159.FStar_Syntax_Syntax.n in
            match uu____3158 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____3174 = traverse f pol e t1 in
                (match uu____3174 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____3201 = traverse f pol e t1 in
                (match uu____3201 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3223;
                   FStar_Syntax_Syntax.vars = uu____3224;_},(p,uu____3226)::
                 (q,uu____3228)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3268 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3268 in
                let uu____3269 = traverse f (flip pol) e p in
                (match uu____3269 with
                 | (p',gs1) ->
                     let uu____3288 =
                       let uu____3295 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____3295 q in
                     (match uu____3288 with
                      | (q',gs2) ->
                          let uu____3308 =
                            let uu____3309 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____3309.FStar_Syntax_Syntax.n in
                          (uu____3308, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____3336 = traverse f pol e hd1 in
                (match uu____3336 with
                 | (hd',gs1) ->
                     let uu____3355 =
                       FStar_List.fold_right
                         (fun uu____3393  ->
                            fun uu____3394  ->
                              match (uu____3393, uu____3394) with
                              | ((a,q),(as',gs)) ->
                                  let uu____3475 = traverse f pol e a in
                                  (match uu____3475 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____3355 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____3579 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____3579 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____3593 =
                       let uu____3608 =
                         FStar_List.map
                           (fun uu____3641  ->
                              match uu____3641 with
                              | (bv,aq) ->
                                  let uu____3658 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____3658 with
                                   | (s',gs) ->
                                       (((let uu___186_3688 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___186_3688.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___186_3688.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____3608 in
                     (match uu____3593 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____3752 = traverse f pol e' topen in
                          (match uu____3752 with
                           | (topen',gs2) ->
                               let uu____3771 =
                                 let uu____3772 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____3772.FStar_Syntax_Syntax.n in
                               (uu____3771, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____3151 with
          | (tn',gs) ->
              let t' =
                let uu___187_3795 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___187_3795.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___187_3795.FStar_Syntax_Syntax.vars)
                } in
              let uu____3796 = f pol e t' in
              (match uu____3796 with
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
      (let uu____3855 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3855);
      (let uu____3903 = FStar_ST.op_Bang tacdbg in
       if uu____3903
       then
         let uu____3950 =
           let uu____3951 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____3951
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____3952 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____3950
           uu____3952
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____3981 = traverse by_tactic_interp Pos env goal in
       match uu____3981 with
       | (t',gs) ->
           ((let uu____4003 = FStar_ST.op_Bang tacdbg in
             if uu____4003
             then
               let uu____4050 =
                 let uu____4051 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4051
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4052 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4050 uu____4052
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4099  ->
                    fun g  ->
                      match uu____4099 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4144 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4144 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4147 =
                                  let uu____4148 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4148 in
                                failwith uu____4147
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4151 = FStar_ST.op_Bang tacdbg in
                            if uu____4151
                            then
                              let uu____4198 = FStar_Util.string_of_int n1 in
                              let uu____4199 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4198 uu____4199
                            else ());
                           (let gt' =
                              let uu____4202 =
                                let uu____4203 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4203 in
                              FStar_TypeChecker_Util.label uu____4202
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4218 = s1 in
             match uu____4218 with
             | (uu____4239,gs1) ->
                 let uu____4257 =
                   let uu____4264 = FStar_Options.peek () in
                   (env, t', uu____4264) in
                 uu____4257 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4276 =
        let uu____4277 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4277 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4276 [FStar_Syntax_Syntax.U_zero] in
    let uu____4278 =
      let uu____4279 =
        let uu____4280 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4281 =
          let uu____4284 = FStar_Syntax_Syntax.as_arg a in [uu____4284] in
        uu____4280 :: uu____4281 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4279 in
    uu____4278 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4300 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4300);
        (let uu____4347 =
           let uu____4354 = reify_tactic tau in
           run_tactic_on_typ uu____4354 env typ in
         match uu____4347 with
         | (gs,w) ->
             let uu____4361 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4365 =
                      let uu____4366 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4366 in
                    Prims.op_Negation uu____4365) gs in
             if uu____4361
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)