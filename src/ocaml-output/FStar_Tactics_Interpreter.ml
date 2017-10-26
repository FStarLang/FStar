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
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1898)::(r,uu____1900)::[] ->
          let uu____1927 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1927
            (fun ps1  ->
               let uu____1933 = FStar_Syntax_Embeddings.unembed_range r in
               FStar_Util.bind_opt uu____1933
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1 in
                    let uu____1941 =
                      let uu____1942 =
                        FStar_TypeChecker_Normalize.psc_range psc in
                      FStar_Tactics_Embedding.embed_proofstate uu____1942 ps' in
                    FStar_Pervasives_Native.Some uu____1941))
      | uu____1943 ->
          failwith "Unexpected application of set_proofstate_range" in
    let set_proofstate_range_step =
      let nm =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.set_proofstate_range" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "2");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation =
          set_proofstate_range_interp
      } in
    let tracepoint_step =
      let nm = FStar_Ident.lid_of_str "FStar.Tactics.Types.tracepoint" in
      {
        FStar_TypeChecker_Normalize.name = nm;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = true;
        FStar_TypeChecker_Normalize.interpretation = tracepoint_interp
      } in
    let put1 rng t =
      let uu___186_1957 = t in
      {
        FStar_Syntax_Syntax.n = (uu___186_1957.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___186_1957.FStar_Syntax_Syntax.vars)
      } in
    let get1 t = FStar_Pervasives_Native.Some t in
    let uu____1964 =
      let uu____1967 =
        mktac2 "__fail" (fun uu____1969  -> FStar_Tactics_Basic.fail) get1
          FStar_Syntax_Embeddings.unembed_string put1
          FStar_Syntax_Syntax.t_unit in
      let uu____1970 =
        let uu____1973 =
          mktac0 "__trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
        let uu____1974 =
          let uu____1977 =
            let uu____1978 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit in
            mktac2 "__trytac" (fun uu____1988  -> FStar_Tactics_Basic.trytac)
              get1 (unembed_tactic_0' get1) uu____1978
              FStar_Syntax_Syntax.t_unit in
          let uu____1995 =
            let uu____1998 =
              mktac0 "__intro" FStar_Tactics_Basic.intro
                FStar_Reflection_Basic.embed_binder
                FStar_Reflection_Data.fstar_refl_binder in
            let uu____1999 =
              let uu____2002 =
                let uu____2003 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                let uu____2010 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec uu____2003
                  uu____2010 in
              let uu____2021 =
                let uu____2024 =
                  let uu____2025 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step in
                  mktac1 "__norm" FStar_Tactics_Basic.norm uu____2025
                    FStar_Syntax_Embeddings.embed_unit
                    FStar_Syntax_Syntax.t_unit in
                let uu____2036 =
                  let uu____2039 =
                    let uu____2040 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step in
                    mktac3 "__norm_term_env"
                      FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Basic.unembed_env uu____2040
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_term
                      FStar_Syntax_Syntax.t_term in
                  let uu____2051 =
                    let uu____2054 =
                      let uu____2055 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step in
                      mktac2 "__norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____2055
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____2066 =
                      let uu____2069 =
                        mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Basic.unembed_binder
                          FStar_Syntax_Embeddings.unembed_string
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____2070 =
                        let uu____2073 =
                          mktac1 "__binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Basic.unembed_binder
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____2074 =
                          let uu____2077 =
                            mktac0 "__revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____2078 =
                            let uu____2081 =
                              mktac0 "__clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____2082 =
                              let uu____2085 =
                                mktac1 "__clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Basic.unembed_binder
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____2086 =
                                let uu____2089 =
                                  mktac1 "__rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Basic.unembed_binder
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____2090 =
                                  let uu____2093 =
                                    mktac0 "__smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____2094 =
                                    let uu____2097 =
                                      mktac1 "__exact"
                                        FStar_Tactics_Basic.exact
                                        FStar_Reflection_Basic.unembed_term
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____2098 =
                                      let uu____2101 =
                                        mktac1 "__exact_guard"
                                          FStar_Tactics_Basic.exact_guard
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____2102 =
                                        let uu____2105 =
                                          mktac1 "__apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____2106 =
                                          let uu____2109 =
                                            mktac1 "__apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Basic.unembed_term
                                              FStar_Syntax_Embeddings.embed_unit
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____2110 =
                                            let uu____2113 =
                                              mktac1 "__apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Basic.unembed_term
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____2114 =
                                              let uu____2117 =
                                                let uu____2118 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit in
                                                mktac5 "__divide"
                                                  (fun uu____2135  ->
                                                     fun uu____2136  ->
                                                       FStar_Tactics_Basic.divide)
                                                  get1 get1
                                                  FStar_Syntax_Embeddings.unembed_int
                                                  (unembed_tactic_0' get1)
                                                  (unembed_tactic_0' get1)
                                                  uu____2118
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____2143 =
                                                let uu____2146 =
                                                  mktac1 "__set_options"
                                                    FStar_Tactics_Basic.set_options
                                                    FStar_Syntax_Embeddings.unembed_string
                                                    FStar_Syntax_Embeddings.embed_unit
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____2147 =
                                                  let uu____2150 =
                                                    mktac2 "__seq"
                                                      FStar_Tactics_Basic.seq
                                                      (unembed_tactic_0'
                                                         FStar_Syntax_Embeddings.unembed_unit)
                                                      (unembed_tactic_0'
                                                         FStar_Syntax_Embeddings.unembed_unit)
                                                      FStar_Syntax_Embeddings.embed_unit
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____2155 =
                                                    let uu____2158 =
                                                      mktac1 "__tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Basic.unembed_term
                                                        FStar_Reflection_Basic.embed_term
                                                        FStar_Syntax_Syntax.t_term in
                                                    let uu____2159 =
                                                      let uu____2162 =
                                                        mktac1 "__unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Basic.unembed_term
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____2163 =
                                                        let uu____2166 =
                                                          mktac2 "__unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            get1
                                                            FStar_Reflection_Basic.unembed_term
                                                            put1
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____2167 =
                                                          let uu____2170 =
                                                            mktac1 "__prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____2171 =
                                                            let uu____2174 =
                                                              mktac1
                                                                "__addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.unembed_string
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____2175 =
                                                              let uu____2178
                                                                =
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
                                                              let uu____2183
                                                                =
                                                                let uu____2186
                                                                  =
                                                                  mktac1
                                                                    "__dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____2187
                                                                  =
                                                                  let uu____2190
                                                                    =
                                                                    mktac1
                                                                    "__dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____2191
                                                                    =
                                                                    let uu____2194
                                                                    =
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.unembed_direction
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2197
                                                                    =
                                                                    let uu____2200
                                                                    =
                                                                    mktac0
                                                                    "__trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2201
                                                                    =
                                                                    let uu____2204
                                                                    =
                                                                    mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2205
                                                                    =
                                                                    let uu____2208
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2209
                                                                    =
                                                                    let uu____2212
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2213
                                                                    =
                                                                    let uu____2216
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2217
                                                                    =
                                                                    let uu____2220
                                                                    =
                                                                    let uu____2221
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2228
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    uu____2221
                                                                    uu____2228 in
                                                                    let uu____2239
                                                                    =
                                                                    let uu____2242
                                                                    =
                                                                    mktac0
                                                                    "__top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2243
                                                                    =
                                                                    let uu____2246
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2247
                                                                    =
                                                                    let uu____2250
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2251
                                                                    =
                                                                    let uu____2254
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2255
                                                                    =
                                                                    let uu____2258
                                                                    =
                                                                    let uu____2259
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term in
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    uu____2259
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2270
                                                                    =
                                                                    let uu____2273
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2274
                                                                    =
                                                                    let uu____2277
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____2277;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step] in
                                                                    uu____2273
                                                                    ::
                                                                    uu____2274 in
                                                                    uu____2258
                                                                    ::
                                                                    uu____2270 in
                                                                    uu____2254
                                                                    ::
                                                                    uu____2255 in
                                                                    uu____2250
                                                                    ::
                                                                    uu____2251 in
                                                                    uu____2246
                                                                    ::
                                                                    uu____2247 in
                                                                    uu____2242
                                                                    ::
                                                                    uu____2243 in
                                                                    uu____2220
                                                                    ::
                                                                    uu____2239 in
                                                                    uu____2216
                                                                    ::
                                                                    uu____2217 in
                                                                    uu____2212
                                                                    ::
                                                                    uu____2213 in
                                                                    uu____2208
                                                                    ::
                                                                    uu____2209 in
                                                                    uu____2204
                                                                    ::
                                                                    uu____2205 in
                                                                    uu____2200
                                                                    ::
                                                                    uu____2201 in
                                                                    uu____2194
                                                                    ::
                                                                    uu____2197 in
                                                                  uu____2190
                                                                    ::
                                                                    uu____2191 in
                                                                uu____2186 ::
                                                                  uu____2187 in
                                                              uu____2178 ::
                                                                uu____2183 in
                                                            uu____2174 ::
                                                              uu____2175 in
                                                          uu____2170 ::
                                                            uu____2171 in
                                                        uu____2166 ::
                                                          uu____2167 in
                                                      uu____2162 ::
                                                        uu____2163 in
                                                    uu____2158 :: uu____2159 in
                                                  uu____2150 :: uu____2155 in
                                                uu____2146 :: uu____2147 in
                                              uu____2117 :: uu____2143 in
                                            uu____2113 :: uu____2114 in
                                          uu____2109 :: uu____2110 in
                                        uu____2105 :: uu____2106 in
                                      uu____2101 :: uu____2102 in
                                    uu____2097 :: uu____2098 in
                                  uu____2093 :: uu____2094 in
                                uu____2089 :: uu____2090 in
                              uu____2085 :: uu____2086 in
                            uu____2081 :: uu____2082 in
                          uu____2077 :: uu____2078 in
                        uu____2073 :: uu____2074 in
                      uu____2069 :: uu____2070 in
                    uu____2054 :: uu____2066 in
                  uu____2039 :: uu____2051 in
                uu____2024 :: uu____2036 in
              uu____2002 :: uu____2021 in
            uu____1998 :: uu____1999 in
          uu____1977 :: uu____1995 in
        uu____1973 :: uu____1974 in
      uu____1967 :: uu____1970 in
    FStar_List.append uu____1964
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
             let uu____2300 =
               let uu____2301 =
                 let uu____2302 =
                   let uu____2303 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____2303 in
                 [uu____2302] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2301 in
             uu____2300 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2310 = FStar_ST.op_Bang tacdbg in
            if uu____2310
            then
              let uu____2357 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2357
            else ());
           (let result =
              let uu____2360 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2360 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2364 = FStar_ST.op_Bang tacdbg in
             if uu____2364
             then
               let uu____2411 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2411
             else ());
            (let uu____2413 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2413 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2456 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2456
                   (fun uu____2460  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2483 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2483
                   (fun uu____2487  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2500 =
                   let uu____2501 =
                     let uu____2506 =
                       let uu____2507 =
                         FStar_Syntax_Print.term_to_string result in
                       FStar_Util.format1
                         "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                         uu____2507 in
                     (uu____2506,
                       ((proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)) in
                   FStar_Errors.Error uu____2501 in
                 FStar_Exn.raise uu____2500)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2516 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
        uu____2516
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2570  ->
             match uu____2570 with
             | (r,uu____2588,uv,uu____2590,ty,rng) ->
                 let uu____2593 =
                   let uu____2594 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2595 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2594 uu____2595 r in
                 (uu____2593, rng)) is in
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
        (let uu____2643 = FStar_ST.op_Bang tacdbg in
         if uu____2643
         then
           let uu____2690 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2690
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1 in
          let uu____2697 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____2697 with
          | (env1,uu____2711) ->
              let env2 =
                let uu___187_2717 = env1 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___187_2717.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___187_2717.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___187_2717.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___187_2717.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___187_2717.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___187_2717.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___187_2717.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___187_2717.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___187_2717.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___187_2717.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___187_2717.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___187_2717.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___187_2717.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___187_2717.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___187_2717.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___187_2717.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___187_2717.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___187_2717.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___187_2717.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___187_2717.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___187_2717.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___187_2717.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___187_2717.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___187_2717.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___187_2717.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___187_2717.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___187_2717.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___187_2717.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___187_2717.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___187_2717.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___187_2717.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___187_2717.FStar_TypeChecker_Env.dsenv)
                } in
              let uu____2718 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
              (match uu____2718 with
               | (ps,w) ->
                   ((let uu____2732 = FStar_ST.op_Bang tacdbg in
                     if uu____2732
                     then
                       let uu____2779 = FStar_Syntax_Print.term_to_string typ in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2779
                     else ());
                    (let uu____2781 = FStar_Tactics_Basic.run tau ps in
                     match uu____2781 with
                     | FStar_Tactics_Result.Success (uu____2790,ps1) ->
                         ((let uu____2793 = FStar_ST.op_Bang tacdbg in
                           if uu____2793
                           then
                             let uu____2840 =
                               FStar_Syntax_Print.term_to_string w in
                             FStar_Util.print1
                               "Tactic generated proofterm %s\n" uu____2840
                           else ());
                          FStar_List.iter
                            (fun g  ->
                               let uu____2847 =
                                 FStar_Tactics_Basic.is_irrelevant g in
                               if uu____2847
                               then
                                 let uu____2848 =
                                   FStar_TypeChecker_Rel.teq_nosmt
                                     g.FStar_Tactics_Types.context
                                     g.FStar_Tactics_Types.witness
                                     FStar_Syntax_Util.exp_unit in
                                 (if uu____2848
                                  then ()
                                  else
                                    (let uu____2850 =
                                       let uu____2851 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Types.witness in
                                       FStar_Util.format1
                                         "Irrelevant tactic witness does not unify with (): %s"
                                         uu____2851 in
                                     failwith uu____2850))
                               else ())
                            (FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals);
                          (let g =
                             let uu___188_2854 =
                               FStar_TypeChecker_Rel.trivial_guard in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___188_2854.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___188_2854.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (uu___188_2854.FStar_TypeChecker_Env.univ_ineqs);
                               FStar_TypeChecker_Env.implicits =
                                 (ps1.FStar_Tactics_Types.all_implicits)
                             } in
                           let g1 =
                             let uu____2856 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____2856
                               FStar_TypeChecker_Rel.resolve_implicits_tac in
                           report_implicits ps1
                             g1.FStar_TypeChecker_Env.implicits;
                           ((FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals), w)))
                     | FStar_Tactics_Result.Failed (s,ps1) ->
                         ((let uu____2863 =
                             let uu____2864 =
                               FStar_TypeChecker_Normalize.psc_subst
                                 ps1.FStar_Tactics_Types.psc in
                             FStar_Tactics_Types.subst_proof_state uu____2864
                               ps1 in
                           FStar_Tactics_Basic.dump_proofstate uu____2863
                             "at the time of failure");
                          (let uu____2865 =
                             let uu____2866 =
                               let uu____2871 =
                                 FStar_Util.format1 "user tactic failed: %s"
                                   s in
                               (uu____2871, (typ.FStar_Syntax_Syntax.pos)) in
                             FStar_Errors.Error uu____2866 in
                           FStar_Exn.raise uu____2865)))))))
type pol =
  | Pos
  | Neg[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2882 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2887 -> false
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
        let uu____2916 = FStar_Syntax_Util.head_and_args t in
        match uu____2916 with
        | (hd1,args) ->
            let uu____2959 =
              let uu____2972 =
                let uu____2973 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2973.FStar_Syntax_Syntax.n in
              (uu____2972, args) in
            (match uu____2959 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2992))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 if pol = Pos
                 then
                   let uu____3061 = run_tactic_on_typ tactic e assertion in
                   (match uu____3061 with
                    | (gs,uu____3075) -> (FStar_Syntax_Util.t_true, gs))
                 else (assertion, [])
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 if pol = Pos
                 then
                   let uu____3127 =
                     let uu____3130 =
                       let uu____3131 =
                         FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                       FStar_All.pipe_left FStar_Pervasives_Native.fst
                         uu____3131 in
                     [uu____3130] in
                   (FStar_Syntax_Util.t_true, uu____3127)
                 else (assertion, [])
             | uu____3147 -> (t, []))
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
          let uu____3217 =
            let uu____3224 =
              let uu____3225 = FStar_Syntax_Subst.compress t in
              uu____3225.FStar_Syntax_Syntax.n in
            match uu____3224 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let uu____3240 = traverse f pol e t1 in
                (match uu____3240 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_uinst (t', us)), gs))
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let uu____3267 = traverse f pol e t1 in
                (match uu____3267 with
                 | (t',gs) -> ((FStar_Syntax_Syntax.Tm_meta (t', m)), gs))
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3289;
                   FStar_Syntax_Syntax.vars = uu____3290;_},(p,uu____3292)::
                 (q,uu____3294)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3334 = FStar_Syntax_Util.mk_squash p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3334 in
                let uu____3335 = traverse f (flip pol) e p in
                (match uu____3335 with
                 | (p',gs1) ->
                     let uu____3354 =
                       let uu____3361 = FStar_TypeChecker_Env.push_bv e x in
                       traverse f pol uu____3361 q in
                     (match uu____3354 with
                      | (q',gs2) ->
                          let uu____3374 =
                            let uu____3375 = FStar_Syntax_Util.mk_imp p' q' in
                            uu____3375.FStar_Syntax_Syntax.n in
                          (uu____3374, (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let uu____3402 = traverse f pol e hd1 in
                (match uu____3402 with
                 | (hd',gs1) ->
                     let uu____3421 =
                       FStar_List.fold_right
                         (fun uu____3459  ->
                            fun uu____3460  ->
                              match (uu____3459, uu____3460) with
                              | ((a,q),(as',gs)) ->
                                  let uu____3541 = traverse f pol e a in
                                  (match uu____3541 with
                                   | (a',gs') ->
                                       (((a', q) :: as'),
                                         (FStar_List.append gs gs')))) args
                         ([], []) in
                     (match uu____3421 with
                      | (as',gs2) ->
                          ((FStar_Syntax_Syntax.Tm_app (hd', as')),
                            (FStar_List.append gs1 gs2))))
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____3645 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____3645 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let uu____3659 =
                       let uu____3674 =
                         FStar_List.map
                           (fun uu____3707  ->
                              match uu____3707 with
                              | (bv,aq) ->
                                  let uu____3724 =
                                    traverse f (flip pol) e
                                      bv.FStar_Syntax_Syntax.sort in
                                  (match uu____3724 with
                                   | (s',gs) ->
                                       (((let uu___189_3754 = bv in
                                          {
                                            FStar_Syntax_Syntax.ppname =
                                              (uu___189_3754.FStar_Syntax_Syntax.ppname);
                                            FStar_Syntax_Syntax.index =
                                              (uu___189_3754.FStar_Syntax_Syntax.index);
                                            FStar_Syntax_Syntax.sort = s'
                                          }), aq), gs))) bs1 in
                       FStar_All.pipe_left FStar_List.unzip uu____3674 in
                     (match uu____3659 with
                      | (bs2,gs1) ->
                          let gs11 = FStar_List.flatten gs1 in
                          let uu____3818 = traverse f pol e' topen in
                          (match uu____3818 with
                           | (topen',gs2) ->
                               let uu____3837 =
                                 let uu____3838 =
                                   FStar_Syntax_Util.abs bs2 topen' k in
                                 uu____3838.FStar_Syntax_Syntax.n in
                               (uu____3837, (FStar_List.append gs11 gs2)))))
            | x -> (x, []) in
          match uu____3217 with
          | (tn',gs) ->
              let t' =
                let uu___190_3861 = t in
                {
                  FStar_Syntax_Syntax.n = tn';
                  FStar_Syntax_Syntax.pos =
                    (uu___190_3861.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___190_3861.FStar_Syntax_Syntax.vars)
                } in
              let uu____3862 = f pol e t' in
              (match uu____3862 with
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
      (let uu____3921 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____3921);
      (let uu____3969 = FStar_ST.op_Bang tacdbg in
       if uu____3969
       then
         let uu____4016 =
           let uu____4017 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____4017
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____4018 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4016
           uu____4018
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____4047 = traverse by_tactic_interp Pos env goal in
       match uu____4047 with
       | (t',gs) ->
           ((let uu____4069 = FStar_ST.op_Bang tacdbg in
             if uu____4069
             then
               let uu____4116 =
                 let uu____4117 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4117
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4118 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4116 uu____4118
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4165  ->
                    fun g  ->
                      match uu____4165 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4210 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4210 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4213 =
                                  let uu____4214 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4214 in
                                failwith uu____4213
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4217 = FStar_ST.op_Bang tacdbg in
                            if uu____4217
                            then
                              let uu____4264 = FStar_Util.string_of_int n1 in
                              let uu____4265 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4264 uu____4265
                            else ());
                           (let gt' =
                              let uu____4268 =
                                let uu____4269 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4269 in
                              FStar_TypeChecker_Util.label uu____4268
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4284 = s1 in
             match uu____4284 with
             | (uu____4305,gs1) ->
                 let uu____4323 =
                   let uu____4330 = FStar_Options.peek () in
                   (env, t', uu____4330) in
                 uu____4323 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4342 =
        let uu____4343 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4343 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4342 [FStar_Syntax_Syntax.U_zero] in
    let uu____4344 =
      let uu____4345 =
        let uu____4346 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4347 =
          let uu____4350 = FStar_Syntax_Syntax.as_arg a in [uu____4350] in
        uu____4346 :: uu____4347 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4345 in
    uu____4344 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4366 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4366);
        (let uu____4413 =
           let uu____4420 = reify_tactic tau in
           run_tactic_on_typ uu____4420 env typ in
         match uu____4413 with
         | (gs,w) ->
             let uu____4427 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4431 =
                      let uu____4432 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4432 in
                    Prims.op_Negation uu____4431) gs in
             if uu____4427
             then
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("synthesis left open goals",
                      (typ.FStar_Syntax_Syntax.pos)))
             else w)