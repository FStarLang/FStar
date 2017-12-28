
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
              | (embedded_state,uu____63)::[] ->
                  let uu____80 =
                    FStar_Tactics_Embedding.unembed_proofstate embedded_state in
                  FStar_Util.bind_opt uu____80
                    (fun ps  ->
                       let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                       FStar_Tactics_Basic.log ps1
                         (fun uu____94  ->
                            let uu____95 = FStar_Ident.string_of_lid nm in
                            let uu____96 =
                              FStar_Syntax_Print.args_to_string args in
                            FStar_Util.print2 "Reached %s, args are: %s\n"
                              uu____95 uu____96);
                       (let res = FStar_Tactics_Basic.run t ps1 in
                        let uu____100 =
                          let uu____101 =
                            FStar_TypeChecker_Normalize.psc_range psc in
                          FStar_Tactics_Embedding.embed_result embed_r t_r
                            uu____101 res in
                        FStar_Pervasives_Native.Some uu____100))
              | uu____108 ->
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
                | (a,uu____180)::(embedded_state,uu____182)::[] ->
                    let uu____209 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____209
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____222  ->
                              let uu____223 = FStar_Ident.string_of_lid nm in
                              let uu____224 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____223 uu____224);
                         (let uu____225 = unembed_a a in
                          FStar_Util.bind_opt uu____225
                            (fun a1  ->
                               let res =
                                 let uu____237 = t a1 in
                                 FStar_Tactics_Basic.run uu____237 ps1 in
                               let uu____240 =
                                 let uu____241 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____241 res in
                               FStar_Pervasives_Native.Some uu____240)))
                | uu____248 ->
                    let uu____249 =
                      let uu____250 = FStar_Ident.string_of_lid nm in
                      let uu____251 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____250 uu____251 in
                    failwith uu____249
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
                | (a,uu____328)::(embedded_state,uu____330)::[] ->
                    let uu____357 =
                      FStar_Tactics_Embedding.unembed_proofstate
                        embedded_state in
                    FStar_Util.bind_opt uu____357
                      (fun ps  ->
                         let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                         FStar_Tactics_Basic.log ps1
                           (fun uu____370  ->
                              let uu____371 = FStar_Ident.string_of_lid nm in
                              let uu____372 =
                                FStar_Syntax_Print.term_to_string
                                  embedded_state in
                              FStar_Util.print2 "Reached %s, goals are: %s\n"
                                uu____371 uu____372);
                         (let uu____373 = unembed_a a in
                          FStar_Util.bind_opt uu____373
                            (fun a1  ->
                               let res =
                                 let uu____385 = t psc a1 in
                                 FStar_Tactics_Basic.run uu____385 ps1 in
                               let uu____388 =
                                 let uu____389 =
                                   FStar_TypeChecker_Normalize.psc_range psc in
                                 FStar_Tactics_Embedding.embed_result embed_r
                                   t_r uu____389 res in
                               FStar_Pervasives_Native.Some uu____388)))
                | uu____396 ->
                    let uu____397 =
                      let uu____398 = FStar_Ident.string_of_lid nm in
                      let uu____399 = FStar_Syntax_Print.args_to_string args in
                      FStar_Util.format2
                        "Unexpected application of tactic primitive %s %s"
                        uu____398 uu____399 in
                    failwith uu____397
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
                  | (a,uu____491)::(b,uu____493)::(embedded_state,uu____495)::[]
                      ->
                      let uu____532 =
                        FStar_Tactics_Embedding.unembed_proofstate
                          embedded_state in
                      FStar_Util.bind_opt uu____532
                        (fun ps  ->
                           let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                           FStar_Tactics_Basic.log ps1
                             (fun uu____545  ->
                                let uu____546 = FStar_Ident.string_of_lid nm in
                                let uu____547 =
                                  FStar_Syntax_Print.term_to_string
                                    embedded_state in
                                FStar_Util.print2
                                  "Reached %s, goals are: %s\n" uu____546
                                  uu____547);
                           (let uu____548 = unembed_a a in
                            FStar_Util.bind_opt uu____548
                              (fun a1  ->
                                 let uu____556 = unembed_b b in
                                 FStar_Util.bind_opt uu____556
                                   (fun b1  ->
                                      let res =
                                        let uu____568 = t a1 b1 in
                                        FStar_Tactics_Basic.run uu____568 ps1 in
                                      let uu____571 =
                                        let uu____572 =
                                          FStar_TypeChecker_Normalize.psc_range
                                            psc in
                                        FStar_Tactics_Embedding.embed_result
                                          embed_r t_r uu____572 res in
                                      FStar_Pervasives_Native.Some uu____571))))
                  | uu____579 ->
                      let uu____580 =
                        let uu____581 = FStar_Ident.string_of_lid nm in
                        let uu____582 =
                          FStar_Syntax_Print.args_to_string args in
                        FStar_Util.format2
                          "Unexpected application of tactic primitive %s %s"
                          uu____581 uu____582 in
                      failwith uu____580
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
                    | (a,uu____694)::(b,uu____696)::(c,uu____698)::(embedded_state,uu____700)::[]
                        ->
                        let uu____747 =
                          FStar_Tactics_Embedding.unembed_proofstate
                            embedded_state in
                        FStar_Util.bind_opt uu____747
                          (fun ps  ->
                             let ps1 = FStar_Tactics_Types.set_ps_psc psc ps in
                             FStar_Tactics_Basic.log ps1
                               (fun uu____760  ->
                                  let uu____761 =
                                    FStar_Ident.string_of_lid nm in
                                  let uu____762 =
                                    FStar_Syntax_Print.term_to_string
                                      embedded_state in
                                  FStar_Util.print2
                                    "Reached %s, goals are: %s\n" uu____761
                                    uu____762);
                             (let uu____763 = unembed_a a in
                              FStar_Util.bind_opt uu____763
                                (fun a1  ->
                                   let uu____771 = unembed_b b in
                                   FStar_Util.bind_opt uu____771
                                     (fun b1  ->
                                        let uu____779 = unembed_c c in
                                        FStar_Util.bind_opt uu____779
                                          (fun c1  ->
                                             let res =
                                               let uu____791 = t a1 b1 c1 in
                                               FStar_Tactics_Basic.run
                                                 uu____791 ps1 in
                                             let uu____794 =
                                               let uu____795 =
                                                 FStar_TypeChecker_Normalize.psc_range
                                                   psc in
                                               FStar_Tactics_Embedding.embed_result
                                                 embed_r t_r uu____795 res in
                                             FStar_Pervasives_Native.Some
                                               uu____794)))))
                    | uu____802 ->
                        let uu____803 =
                          let uu____804 = FStar_Ident.string_of_lid nm in
                          let uu____805 =
                            FStar_Syntax_Print.args_to_string args in
                          FStar_Util.format2
                            "Unexpected application of tactic primitive %s %s"
                            uu____804 uu____805 in
                        failwith uu____803
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
                        | (a,uu____957)::(b,uu____959)::(c,uu____961)::
                            (d,uu____963)::(e,uu____965)::(embedded_state,uu____967)::[]
                            ->
                            let uu____1034 =
                              FStar_Tactics_Embedding.unembed_proofstate
                                embedded_state in
                            FStar_Util.bind_opt uu____1034
                              (fun ps  ->
                                 let ps1 =
                                   FStar_Tactics_Types.set_ps_psc psc ps in
                                 FStar_Tactics_Basic.log ps1
                                   (fun uu____1047  ->
                                      let uu____1048 =
                                        FStar_Ident.string_of_lid nm in
                                      let uu____1049 =
                                        FStar_Syntax_Print.term_to_string
                                          embedded_state in
                                      FStar_Util.print2
                                        "Reached %s, goals are: %s\n"
                                        uu____1048 uu____1049);
                                 (let uu____1050 = unembed_a a in
                                  FStar_Util.bind_opt uu____1050
                                    (fun a1  ->
                                       let uu____1058 = unembed_b b in
                                       FStar_Util.bind_opt uu____1058
                                         (fun b1  ->
                                            let uu____1066 = unembed_c c in
                                            FStar_Util.bind_opt uu____1066
                                              (fun c1  ->
                                                 let uu____1074 = unembed_d d in
                                                 FStar_Util.bind_opt
                                                   uu____1074
                                                   (fun d1  ->
                                                      let uu____1082 =
                                                        unembed_e e in
                                                      FStar_Util.bind_opt
                                                        uu____1082
                                                        (fun e1  ->
                                                           let res =
                                                             let uu____1094 =
                                                               t a1 b1 c1 d1
                                                                 e1 in
                                                             FStar_Tactics_Basic.run
                                                               uu____1094 ps1 in
                                                           let uu____1097 =
                                                             let uu____1098 =
                                                               FStar_TypeChecker_Normalize.psc_range
                                                                 psc in
                                                             FStar_Tactics_Embedding.embed_result
                                                               embed_r t_r
                                                               uu____1098 res in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1097)))))))
                        | uu____1105 ->
                            let uu____1106 =
                              let uu____1107 = FStar_Ident.string_of_lid nm in
                              let uu____1108 =
                                FStar_Syntax_Print.args_to_string args in
                              FStar_Util.format2
                                "Unexpected application of tactic primitive %s %s"
                                uu____1107 uu____1108 in
                            failwith uu____1106
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
  fun uu____1160  ->
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
      | (ps,uu____1694)::[] ->
          let uu____1711 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1711
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1719 =
                 let uu____1720 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1721 = FStar_Tactics_Types.decr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1720
                   uu____1721 in
               FStar_Pervasives_Native.Some uu____1719)
      | uu____1722 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1726 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1726;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1739)::[] ->
          let uu____1756 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1756
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1764 =
                 let uu____1765 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1766 = FStar_Tactics_Types.incr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1765
                   uu____1766 in
               FStar_Pervasives_Native.Some uu____1764)
      | uu____1767 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1771 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1771;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1788)::[] ->
          let uu____1805 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1805
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1818 -> failwith "Unexpected application of tracepoint" in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1835)::(r,uu____1837)::[] ->
          let uu____1864 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1864
            (fun ps1  ->
               let uu____1870 = FStar_Syntax_Embeddings.unembed_range r in
               FStar_Util.bind_opt uu____1870
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1 in
                    let uu____1878 =
                      let uu____1879 =
                        FStar_TypeChecker_Normalize.psc_range psc in
                      FStar_Tactics_Embedding.embed_proofstate uu____1879 ps' in
                    FStar_Pervasives_Native.Some uu____1878))
      | uu____1880 ->
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
      let uu___62_1894 = t in
      {
        FStar_Syntax_Syntax.n = (uu___62_1894.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___62_1894.FStar_Syntax_Syntax.vars)
      } in
    let get1 t = FStar_Pervasives_Native.Some t in
    let uu____1901 =
      let uu____1904 =
        mktac2 "__fail" (fun uu____1906  -> FStar_Tactics_Basic.fail) get1
          FStar_Syntax_Embeddings.unembed_string put1
          FStar_Syntax_Syntax.t_unit in
      let uu____1907 =
        let uu____1910 =
          mktac0 "__trivial" FStar_Tactics_Basic.trivial
            FStar_Syntax_Embeddings.embed_unit FStar_Syntax_Syntax.t_unit in
        let uu____1911 =
          let uu____1914 =
            let uu____1915 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit in
            mktac2 "__trytac" (fun uu____1925  -> FStar_Tactics_Basic.trytac)
              get1 (unembed_tactic_0' get1) uu____1915
              FStar_Syntax_Syntax.t_unit in
          let uu____1932 =
            let uu____1935 =
              mktac0 "__intro" FStar_Tactics_Basic.intro
                FStar_Reflection_Basic.embed_binder
                FStar_Reflection_Data.fstar_refl_binder in
            let uu____1936 =
              let uu____1939 =
                let uu____1940 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                let uu____1947 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                mktac0 "__intro_rec" FStar_Tactics_Basic.intro_rec uu____1940
                  uu____1947 in
              let uu____1958 =
                let uu____1961 =
                  let uu____1962 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step in
                  mktac1 "__norm" FStar_Tactics_Basic.norm uu____1962
                    FStar_Syntax_Embeddings.embed_unit
                    FStar_Syntax_Syntax.t_unit in
                let uu____1973 =
                  let uu____1976 =
                    let uu____1977 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step in
                    mktac3 "__norm_term_env"
                      FStar_Tactics_Basic.norm_term_env
                      FStar_Reflection_Basic.unembed_env uu____1977
                      FStar_Reflection_Basic.unembed_term
                      FStar_Reflection_Basic.embed_term
                      FStar_Syntax_Syntax.t_term in
                  let uu____1988 =
                    let uu____1991 =
                      let uu____1992 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step in
                      mktac2 "__norm_binder_type"
                        FStar_Tactics_Basic.norm_binder_type uu____1992
                        FStar_Reflection_Basic.unembed_binder
                        FStar_Syntax_Embeddings.embed_unit
                        FStar_Syntax_Syntax.t_unit in
                    let uu____2003 =
                      let uu____2006 =
                        mktac2 "__rename_to" FStar_Tactics_Basic.rename_to
                          FStar_Reflection_Basic.unembed_binder
                          FStar_Syntax_Embeddings.unembed_string
                          FStar_Syntax_Embeddings.embed_unit
                          FStar_Syntax_Syntax.t_unit in
                      let uu____2007 =
                        let uu____2010 =
                          mktac1 "__binder_retype"
                            FStar_Tactics_Basic.binder_retype
                            FStar_Reflection_Basic.unembed_binder
                            FStar_Syntax_Embeddings.embed_unit
                            FStar_Syntax_Syntax.t_unit in
                        let uu____2011 =
                          let uu____2014 =
                            mktac0 "__revert" FStar_Tactics_Basic.revert
                              FStar_Syntax_Embeddings.embed_unit
                              FStar_Syntax_Syntax.t_unit in
                          let uu____2015 =
                            let uu____2018 =
                              mktac0 "__clear_top"
                                FStar_Tactics_Basic.clear_top
                                FStar_Syntax_Embeddings.embed_unit
                                FStar_Syntax_Syntax.t_unit in
                            let uu____2019 =
                              let uu____2022 =
                                mktac1 "__clear" FStar_Tactics_Basic.clear
                                  FStar_Reflection_Basic.unembed_binder
                                  FStar_Syntax_Embeddings.embed_unit
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____2023 =
                                let uu____2026 =
                                  mktac1 "__rewrite"
                                    FStar_Tactics_Basic.rewrite
                                    FStar_Reflection_Basic.unembed_binder
                                    FStar_Syntax_Embeddings.embed_unit
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____2027 =
                                  let uu____2030 =
                                    mktac0 "__smt" FStar_Tactics_Basic.smt
                                      FStar_Syntax_Embeddings.embed_unit
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____2031 =
                                    let uu____2034 =
                                      mktac0 "__refine_intro"
                                        FStar_Tactics_Basic.refine_intro
                                        FStar_Syntax_Embeddings.embed_unit
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____2035 =
                                      let uu____2038 =
                                        mktac3 "__t_exact"
                                          FStar_Tactics_Basic.t_exact
                                          FStar_Syntax_Embeddings.unembed_bool
                                          FStar_Syntax_Embeddings.unembed_bool
                                          FStar_Reflection_Basic.unembed_term
                                          FStar_Syntax_Embeddings.embed_unit
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____2039 =
                                        let uu____2042 =
                                          mktac1 "__apply"
                                            (FStar_Tactics_Basic.apply true)
                                            FStar_Reflection_Basic.unembed_term
                                            FStar_Syntax_Embeddings.embed_unit
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____2043 =
                                          let uu____2046 =
                                            mktac1 "__apply_raw"
                                              (FStar_Tactics_Basic.apply
                                                 false)
                                              FStar_Reflection_Basic.unembed_term
                                              FStar_Syntax_Embeddings.embed_unit
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____2047 =
                                            let uu____2050 =
                                              mktac1 "__apply_lemma"
                                                FStar_Tactics_Basic.apply_lemma
                                                FStar_Reflection_Basic.unembed_term
                                                FStar_Syntax_Embeddings.embed_unit
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____2051 =
                                              let uu____2054 =
                                                let uu____2055 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit in
                                                mktac5 "__divide"
                                                  (fun uu____2072  ->
                                                     fun uu____2073  ->
                                                       FStar_Tactics_Basic.divide)
                                                  get1 get1
                                                  FStar_Syntax_Embeddings.unembed_int
                                                  (unembed_tactic_0' get1)
                                                  (unembed_tactic_0' get1)
                                                  uu____2055
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____2080 =
                                                let uu____2083 =
                                                  mktac1 "__set_options"
                                                    FStar_Tactics_Basic.set_options
                                                    FStar_Syntax_Embeddings.unembed_string
                                                    FStar_Syntax_Embeddings.embed_unit
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____2084 =
                                                  let uu____2087 =
                                                    mktac2 "__seq"
                                                      FStar_Tactics_Basic.seq
                                                      (unembed_tactic_0'
                                                         FStar_Syntax_Embeddings.unembed_unit)
                                                      (unembed_tactic_0'
                                                         FStar_Syntax_Embeddings.unembed_unit)
                                                      FStar_Syntax_Embeddings.embed_unit
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____2092 =
                                                    let uu____2095 =
                                                      mktac1 "__tc"
                                                        FStar_Tactics_Basic.tc
                                                        FStar_Reflection_Basic.unembed_term
                                                        FStar_Reflection_Basic.embed_term
                                                        FStar_Syntax_Syntax.t_term in
                                                    let uu____2096 =
                                                      let uu____2099 =
                                                        mktac1 "__unshelve"
                                                          FStar_Tactics_Basic.unshelve
                                                          FStar_Reflection_Basic.unembed_term
                                                          FStar_Syntax_Embeddings.embed_unit
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____2100 =
                                                        let uu____2103 =
                                                          mktac2 "__unquote"
                                                            FStar_Tactics_Basic.unquote
                                                            get1
                                                            FStar_Reflection_Basic.unembed_term
                                                            put1
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____2104 =
                                                          let uu____2107 =
                                                            mktac1 "__prune"
                                                              FStar_Tactics_Basic.prune
                                                              FStar_Syntax_Embeddings.unembed_string
                                                              FStar_Syntax_Embeddings.embed_unit
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____2108 =
                                                            let uu____2111 =
                                                              mktac1
                                                                "__addns"
                                                                FStar_Tactics_Basic.addns
                                                                FStar_Syntax_Embeddings.unembed_string
                                                                FStar_Syntax_Embeddings.embed_unit
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____2112 =
                                                              let uu____2115
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
                                                              let uu____2120
                                                                =
                                                                let uu____2123
                                                                  =
                                                                  mktac1
                                                                    "__dump"
                                                                    FStar_Tactics_Basic.print_proof_state
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____2124
                                                                  =
                                                                  let uu____2127
                                                                    =
                                                                    mktac1
                                                                    "__dump1"
                                                                    FStar_Tactics_Basic.print_proof_state1
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____2128
                                                                    =
                                                                    let uu____2131
                                                                    =
                                                                    mktac2
                                                                    "__pointwise"
                                                                    FStar_Tactics_Basic.pointwise
                                                                    FStar_Tactics_Embedding.unembed_direction
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit)
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2134
                                                                    =
                                                                    let uu____2137
                                                                    =
                                                                    mktac0
                                                                    "__trefl"
                                                                    FStar_Tactics_Basic.trefl
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2138
                                                                    =
                                                                    let uu____2141
                                                                    =
                                                                    mktac0
                                                                    "__later"
                                                                    FStar_Tactics_Basic.later
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2142
                                                                    =
                                                                    let uu____2145
                                                                    =
                                                                    mktac0
                                                                    "__dup"
                                                                    FStar_Tactics_Basic.dup
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2146
                                                                    =
                                                                    let uu____2149
                                                                    =
                                                                    mktac0
                                                                    "__flip"
                                                                    FStar_Tactics_Basic.flip
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2150
                                                                    =
                                                                    let uu____2153
                                                                    =
                                                                    mktac0
                                                                    "__qed"
                                                                    FStar_Tactics_Basic.qed
                                                                    FStar_Syntax_Embeddings.embed_unit
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2154
                                                                    =
                                                                    let uu____2157
                                                                    =
                                                                    let uu____2158
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2165
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1
                                                                    "__cases"
                                                                    FStar_Tactics_Basic.cases
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    uu____2158
                                                                    uu____2165 in
                                                                    let uu____2176
                                                                    =
                                                                    let uu____2179
                                                                    =
                                                                    mktac0
                                                                    "__top_env"
                                                                    FStar_Tactics_Basic.top_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2180
                                                                    =
                                                                    let uu____2183
                                                                    =
                                                                    mktac0
                                                                    "__cur_env"
                                                                    FStar_Tactics_Basic.cur_env
                                                                    FStar_Reflection_Basic.embed_env
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2184
                                                                    =
                                                                    let uu____2187
                                                                    =
                                                                    mktac0
                                                                    "__cur_goal"
                                                                    FStar_Tactics_Basic.cur_goal'
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2188
                                                                    =
                                                                    let uu____2191
                                                                    =
                                                                    mktac0
                                                                    "__cur_witness"
                                                                    FStar_Tactics_Basic.cur_witness
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2192
                                                                    =
                                                                    let uu____2195
                                                                    =
                                                                    mktac0
                                                                    "__is_guard"
                                                                    FStar_Tactics_Basic.is_guard
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2196
                                                                    =
                                                                    let uu____2199
                                                                    =
                                                                    let uu____2200
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term in
                                                                    mktac2
                                                                    "__uvar_env"
                                                                    FStar_Tactics_Basic.uvar_env
                                                                    FStar_Reflection_Basic.unembed_env
                                                                    uu____2200
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2211
                                                                    =
                                                                    let uu____2214
                                                                    =
                                                                    mktac2
                                                                    "__unify"
                                                                    FStar_Tactics_Basic.unify
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Reflection_Basic.unembed_term
                                                                    FStar_Syntax_Embeddings.embed_bool
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2215
                                                                    =
                                                                    let uu____2218
                                                                    =
                                                                    mktac3
                                                                    "__launch_process"
                                                                    FStar_Tactics_Basic.launch_process
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.unembed_string
                                                                    FStar_Syntax_Embeddings.embed_string
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____2218;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step] in
                                                                    uu____2214
                                                                    ::
                                                                    uu____2215 in
                                                                    uu____2199
                                                                    ::
                                                                    uu____2211 in
                                                                    uu____2195
                                                                    ::
                                                                    uu____2196 in
                                                                    uu____2191
                                                                    ::
                                                                    uu____2192 in
                                                                    uu____2187
                                                                    ::
                                                                    uu____2188 in
                                                                    uu____2183
                                                                    ::
                                                                    uu____2184 in
                                                                    uu____2179
                                                                    ::
                                                                    uu____2180 in
                                                                    uu____2157
                                                                    ::
                                                                    uu____2176 in
                                                                    uu____2153
                                                                    ::
                                                                    uu____2154 in
                                                                    uu____2149
                                                                    ::
                                                                    uu____2150 in
                                                                    uu____2145
                                                                    ::
                                                                    uu____2146 in
                                                                    uu____2141
                                                                    ::
                                                                    uu____2142 in
                                                                    uu____2137
                                                                    ::
                                                                    uu____2138 in
                                                                    uu____2131
                                                                    ::
                                                                    uu____2134 in
                                                                  uu____2127
                                                                    ::
                                                                    uu____2128 in
                                                                uu____2123 ::
                                                                  uu____2124 in
                                                              uu____2115 ::
                                                                uu____2120 in
                                                            uu____2111 ::
                                                              uu____2112 in
                                                          uu____2107 ::
                                                            uu____2108 in
                                                        uu____2103 ::
                                                          uu____2104 in
                                                      uu____2099 ::
                                                        uu____2100 in
                                                    uu____2095 :: uu____2096 in
                                                  uu____2087 :: uu____2092 in
                                                uu____2083 :: uu____2084 in
                                              uu____2054 :: uu____2080 in
                                            uu____2050 :: uu____2051 in
                                          uu____2046 :: uu____2047 in
                                        uu____2042 :: uu____2043 in
                                      uu____2038 :: uu____2039 in
                                    uu____2034 :: uu____2035 in
                                  uu____2030 :: uu____2031 in
                                uu____2026 :: uu____2027 in
                              uu____2022 :: uu____2023 in
                            uu____2018 :: uu____2019 in
                          uu____2014 :: uu____2015 in
                        uu____2010 :: uu____2011 in
                      uu____2006 :: uu____2007 in
                    uu____1991 :: uu____2003 in
                  uu____1976 :: uu____1988 in
                uu____1961 :: uu____1973 in
              uu____1939 :: uu____1958 in
            uu____1935 :: uu____1936 in
          uu____1914 :: uu____1932 in
        uu____1910 :: uu____1911 in
      uu____1904 :: uu____1907 in
    FStar_List.append uu____1901
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
             let uu____2241 =
               let uu____2242 =
                 let uu____2243 =
                   let uu____2244 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____2244 in
                 [uu____2243] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2242 in
             uu____2241 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2251 = FStar_ST.op_Bang tacdbg in
            if uu____2251
            then
              let uu____2300 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2300
            else ());
           (let result =
              let uu____2303 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2303 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2307 = FStar_ST.op_Bang tacdbg in
             if uu____2307
             then
               let uu____2356 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2356
             else ());
            (let uu____2358 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2358 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2401 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2401
                   (fun uu____2405  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2428 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2428
                   (fun uu____2432  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2445 =
                   let uu____2450 =
                     let uu____2451 =
                       FStar_Syntax_Print.term_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2451 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2450) in
                 FStar_Errors.raise_error uu____2445
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2460 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
        uu____2460
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2516  ->
             match uu____2516 with
             | (r,uu____2536,uv,uu____2538,ty,rng) ->
                 let uu____2541 =
                   let uu____2542 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2543 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2542 uu____2543 r in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2541, rng)) is in
      match errs with
      | [] -> ()
      | (e,msg,r)::tl1 ->
          (FStar_Tactics_Basic.dump_proofstate ps
             "failing due to uninstantiated implicits";
           FStar_Errors.add_errors tl1;
           FStar_Errors.raise_error (e, msg) r)
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
        (let uu____2592 = FStar_ST.op_Bang tacdbg in
         if uu____2592
         then
           let uu____2641 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2641
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1 in
          let uu____2648 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____2648 with
          | (env1,uu____2662) ->
              let env2 =
                let uu___63_2668 = env1 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___63_2668.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___63_2668.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___63_2668.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___63_2668.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___63_2668.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___63_2668.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___63_2668.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___63_2668.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___63_2668.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___63_2668.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___63_2668.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___63_2668.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___63_2668.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___63_2668.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___63_2668.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___63_2668.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___63_2668.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___63_2668.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___63_2668.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___63_2668.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___63_2668.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___63_2668.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___63_2668.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___63_2668.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___63_2668.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___63_2668.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___63_2668.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___63_2668.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___63_2668.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___63_2668.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___63_2668.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___63_2668.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___63_2668.FStar_TypeChecker_Env.dep_graph)
                } in
              let uu____2669 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
              (match uu____2669 with
               | (ps,w) ->
                   ((let uu____2683 = FStar_ST.op_Bang tacdbg in
                     if uu____2683
                     then
                       let uu____2732 = FStar_Syntax_Print.term_to_string typ in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2732
                     else ());
                    (let uu____2734 = FStar_Tactics_Basic.run tau ps in
                     match uu____2734 with
                     | FStar_Tactics_Result.Success (uu____2743,ps1) ->
                         ((let uu____2746 = FStar_ST.op_Bang tacdbg in
                           if uu____2746
                           then
                             let uu____2795 =
                               FStar_Syntax_Print.term_to_string w in
                             FStar_Util.print1
                               "Tactic generated proofterm %s\n" uu____2795
                           else ());
                          FStar_List.iter
                            (fun g  ->
                               let uu____2802 =
                                 FStar_Tactics_Basic.is_irrelevant g in
                               if uu____2802
                               then
                                 let uu____2803 =
                                   FStar_TypeChecker_Rel.teq_nosmt
                                     g.FStar_Tactics_Types.context
                                     g.FStar_Tactics_Types.witness
                                     FStar_Syntax_Util.exp_unit in
                                 (if uu____2803
                                  then ()
                                  else
                                    (let uu____2805 =
                                       let uu____2806 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Types.witness in
                                       FStar_Util.format1
                                         "Irrelevant tactic witness does not unify with (): %s"
                                         uu____2806 in
                                     failwith uu____2805))
                               else ())
                            (FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals);
                          (let g =
                             let uu___64_2809 =
                               FStar_TypeChecker_Rel.trivial_guard in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___64_2809.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___64_2809.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (uu___64_2809.FStar_TypeChecker_Env.univ_ineqs);
                               FStar_TypeChecker_Env.implicits =
                                 (ps1.FStar_Tactics_Types.all_implicits)
                             } in
                           let g1 =
                             let uu____2811 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____2811
                               FStar_TypeChecker_Rel.resolve_implicits_tac in
                           report_implicits ps1
                             g1.FStar_TypeChecker_Env.implicits;
                           ((FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals), w)))
                     | FStar_Tactics_Result.Failed (s,ps1) ->
                         ((let uu____2818 =
                             let uu____2819 =
                               FStar_TypeChecker_Normalize.psc_subst
                                 ps1.FStar_Tactics_Types.psc in
                             FStar_Tactics_Types.subst_proof_state uu____2819
                               ps1 in
                           FStar_Tactics_Basic.dump_proofstate uu____2818
                             "at the time of failure");
                          (let uu____2820 =
                             let uu____2825 =
                               FStar_Util.format1 "user tactic failed: %s" s in
                             (FStar_Errors.Fatal_ArgumentLengthMismatch,
                               uu____2825) in
                           FStar_Errors.raise_error uu____2820
                             typ.FStar_Syntax_Syntax.pos)))))))
type pol =
  | Pos
  | Neg
  | Both[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2835 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2839 -> false
let uu___is_Both: pol -> Prims.bool =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2843 -> false
type 'a tres_m =
  | Unchanged of 'a
  | Simplified of ('a,FStar_Tactics_Types.goal Prims.list)
  FStar_Pervasives_Native.tuple2
  | Dual of ('a,'a,FStar_Tactics_Types.goal Prims.list)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_Unchanged: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2892 -> false
let __proj__Unchanged__item___0: 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2928 -> false
let __proj__Simplified__item___0:
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Types.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0
let uu___is_Dual: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2978 -> false
let __proj__Dual__item___0:
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Types.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure: 'Auu____3016 . 'Auu____3016 -> 'Auu____3016 tres_m =
  fun x  -> Unchanged x
let flip: pol -> pol =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both
let by_tactic_interp:
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____3035 = FStar_Syntax_Util.head_and_args t in
        match uu____3035 with
        | (hd1,args) ->
            let uu____3072 =
              let uu____3085 =
                let uu____3086 = FStar_Syntax_Util.un_uinst hd1 in
                uu____3086.FStar_Syntax_Syntax.n in
              (uu____3085, args) in
            (match uu____3072 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____3099))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3162 = run_tactic_on_typ tactic e assertion in
                      (match uu____3162 with
                       | (gs,uu____3170) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____3177 = run_tactic_on_typ tactic e assertion in
                      (match uu____3177 with
                       | (gs,uu____3185) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3236 =
                        let uu____3243 =
                          let uu____3246 =
                            let uu____3247 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3247 in
                          [uu____3246] in
                        (FStar_Syntax_Util.t_true, uu____3243) in
                      Simplified uu____3236
                  | Both  ->
                      let uu____3258 =
                        let uu____3271 =
                          let uu____3274 =
                            let uu____3275 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3275 in
                          [uu____3274] in
                        (assertion, FStar_Syntax_Util.t_true, uu____3271) in
                      Dual uu____3258
                  | Neg  -> Simplified (assertion, []))
             | uu____3296 -> Unchanged t)
let explode:
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Types.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun t  ->
    match t with
    | Unchanged t1 -> (t1, t1, [])
    | Simplified (t1,gs) -> (t1, t1, gs)
    | Dual (tn,tp,gs) -> (tn, tp, gs)
let comb1: 'a 'b . ('a -> 'b) -> 'a tres_m -> 'b tres_m =
  fun f  ->
    fun uu___61_3376  ->
      match uu___61_3376 with
      | Unchanged t -> let uu____3382 = f t in Unchanged uu____3382
      | Simplified (t,gs) ->
          let uu____3389 = let uu____3396 = f t in (uu____3396, gs) in
          Simplified uu____3389
      | Dual (tn,tp,gs) ->
          let uu____3406 =
            let uu____3415 = f tn in
            let uu____3416 = f tp in (uu____3415, uu____3416, gs) in
          Dual uu____3406
let comb2: 'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m
  =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3470 = f t1 t2 in Unchanged uu____3470
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3482 = let uu____3489 = f t1 t2 in (uu____3489, gs) in
            Simplified uu____3482
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3503 = let uu____3510 = f t1 t2 in (uu____3510, gs) in
            Simplified uu____3503
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3529 =
              let uu____3536 = f t1 t2 in
              (uu____3536, (FStar_List.append gs1 gs2)) in
            Simplified uu____3529
        | uu____3539 ->
            let uu____3548 = explode x in
            (match uu____3548 with
             | (n1,p1,gs1) ->
                 let uu____3566 = explode y in
                 (match uu____3566 with
                  | (n2,p2,gs2) ->
                      let uu____3584 =
                        let uu____3593 = f n1 n2 in
                        let uu____3594 = f p1 p2 in
                        (uu____3593, uu____3594, (FStar_List.append gs1 gs2)) in
                      Dual uu____3584))
let comb_list: 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3659 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc in
          aux tl1 uu____3659 in
    aux (FStar_List.rev rs) (tpure [])
let emit: 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3702  -> fun x  -> x) (Simplified ((), gs)) m
let rec traverse:
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3736 =
              let uu____3737 = FStar_Syntax_Subst.compress t in
              uu____3737.FStar_Syntax_Syntax.n in
            match uu____3736 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1 in
                let uu____3749 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us)) in
                uu____3749 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1 in
                let uu____3773 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m)) in
                uu____3773 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3791;
                   FStar_Syntax_Syntax.vars = uu____3792;_},(p,uu____3794)::
                 (q,uu____3796)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3836 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3836 in
                let r1 = traverse f (flip pol) e p in
                let r2 =
                  let uu____3839 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f pol uu____3839 q in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3845 = FStar_Syntax_Util.mk_imp l r in
                       uu____3845.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3849;
                   FStar_Syntax_Syntax.vars = uu____3850;_},(p,uu____3852)::
                 (q,uu____3854)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3894 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3894 in
                let xq =
                  let uu____3896 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3896 in
                let r1 =
                  let uu____3898 = FStar_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu____3898 p in
                let r2 =
                  let uu____3900 = FStar_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu____3900 q in
                (match (r1, r2) with
                 | (Unchanged uu____3903,Unchanged uu____3904) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3914 = FStar_Syntax_Util.mk_iff l r in
                            uu____3914.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3917 ->
                     let uu____3922 = explode r1 in
                     (match uu____3922 with
                      | (pn,pp,gs1) ->
                          let uu____3940 = explode r2 in
                          (match uu____3940 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3961 =
                                   FStar_Syntax_Util.mk_imp pn qp in
                                 let uu____3962 =
                                   FStar_Syntax_Util.mk_imp qn pp in
                                 FStar_Syntax_Util.mk_conj uu____3961
                                   uu____3962 in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1 in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____4014  ->
                       fun r  ->
                         match uu____4014 with
                         | (a,q) ->
                             let r' = traverse f pol e a in
                             comb2
                               (fun a1  -> fun args1  -> (a1, q) :: args1) r'
                               r) args (tpure []) in
                comb2
                  (fun hd2  ->
                     fun args1  -> FStar_Syntax_Syntax.Tm_app (hd2, args1))
                  r0 r1
            | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
                let uu____4132 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____4132 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStar_List.map
                         (fun uu____4166  ->
                            match uu____4166 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort in
                                let uu____4180 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___65_4204 = bv in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___65_4204.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___65_4204.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq)) in
                                uu____4180 r) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol e' topen in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____4224 = FStar_Syntax_Util.abs bs2 t2 k in
                            uu____4224.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4270 = traverse f pol e t1 in
                let uu____4275 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef)) in
                uu____4275 uu____4270
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___66_4313 = t in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___66_4313.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___66_4313.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4320 =
                f pol e
                  (let uu___67_4324 = t in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___67_4324.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___67_4324.FStar_Syntax_Syntax.vars)
                   }) in
              emit gs uu____4320
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___68_4334 = t in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___68_4334.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___68_4334.FStar_Syntax_Syntax.vars)
                   }) in
              let uu____4335 = explode rp in
              (match uu____4335 with
               | (uu____4344,p',gs') ->
                   Dual
                     ((let uu___69_4358 = t in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___69_4358.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___69_4358.FStar_Syntax_Syntax.vars)
                       }), p', (FStar_List.append gs gs')))
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
      (let uu____4393 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____4393);
      (let uu____4443 = FStar_ST.op_Bang tacdbg in
       if uu____4443
       then
         let uu____4492 =
           let uu____4493 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____4493
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____4494 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4492
           uu____4494
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____4523 =
         let uu____4530 = traverse by_tactic_interp Pos env goal in
         match uu____4530 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4548 -> failwith "no" in
       match uu____4523 with
       | (t',gs) ->
           ((let uu____4570 = FStar_ST.op_Bang tacdbg in
             if uu____4570
             then
               let uu____4619 =
                 let uu____4620 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4620
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4621 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4619 uu____4621
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4668  ->
                    fun g  ->
                      match uu____4668 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4713 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4713 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4716 =
                                  let uu____4717 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4717 in
                                failwith uu____4716
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4720 = FStar_ST.op_Bang tacdbg in
                            if uu____4720
                            then
                              let uu____4769 = FStar_Util.string_of_int n1 in
                              let uu____4770 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4769 uu____4770
                            else ());
                           (let gt' =
                              let uu____4773 =
                                let uu____4774 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4774 in
                              FStar_TypeChecker_Util.label uu____4773
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4789 = s1 in
             match uu____4789 with
             | (uu____4810,gs1) ->
                 let uu____4828 =
                   let uu____4835 = FStar_Options.peek () in
                   (env, t', uu____4835) in
                 uu____4828 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4846 =
        let uu____4847 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4847 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4846 [FStar_Syntax_Syntax.U_zero] in
    let uu____4848 =
      let uu____4849 =
        let uu____4850 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4851 =
          let uu____4854 = FStar_Syntax_Syntax.as_arg a in [uu____4854] in
        uu____4850 :: uu____4851 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4849 in
    uu____4848 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4867 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4867);
        (let uu____4916 =
           let uu____4923 = reify_tactic tau in
           run_tactic_on_typ uu____4923 env typ in
         match uu____4916 with
         | (gs,w) ->
             let uu____4930 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4934 =
                      let uu____4935 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4935 in
                    Prims.op_Negation uu____4934) gs in
             if uu____4930
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)