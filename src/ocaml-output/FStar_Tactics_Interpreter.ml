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
    let mktac0 r name f e_r tr =
      mk1 name (Prims.parse_int "1") (mk_tactic_interpretation_0 f e_r tr) in
    let mktac1 a r name f u_a e_r tr =
      mk1 name (Prims.parse_int "2")
        (mk_tactic_interpretation_1 f u_a e_r tr) in
    let mktac2 a b r name f u_a u_b e_r tr =
      mk1 name (Prims.parse_int "3")
        (mk_tactic_interpretation_2 f u_a u_b e_r tr) in
    let mktac3 a b c r name f u_a u_b u_c e_r tr =
      mk1 name (Prims.parse_int "4")
        (mk_tactic_interpretation_3 f u_a u_b u_c e_r tr) in
    let mktac5 a b c d e r name f u_a u_b u_c u_d u_e e_r tr =
      mk1 name (Prims.parse_int "6")
        (mk_tactic_interpretation_5 f u_a u_b u_c u_d u_e e_r tr) in
    let decr_depth_interp psc args =
      match args with
      | (ps,uu____1648)::[] ->
          let uu____1665 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1665
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1673 =
                 let uu____1674 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1675 = FStar_Tactics_Types.decr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1674
                   uu____1675 in
               FStar_Pervasives_Native.Some uu____1673)
      | uu____1676 -> failwith "Unexpected application of decr_depth" in
    let decr_depth_step =
      let uu____1680 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.decr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1680;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = decr_depth_interp
      } in
    let incr_depth_interp psc args =
      match args with
      | (ps,uu____1693)::[] ->
          let uu____1710 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1710
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               let uu____1718 =
                 let uu____1719 = FStar_TypeChecker_Normalize.psc_range psc in
                 let uu____1720 = FStar_Tactics_Types.incr_depth ps2 in
                 FStar_Tactics_Embedding.embed_proofstate uu____1719
                   uu____1720 in
               FStar_Pervasives_Native.Some uu____1718)
      | uu____1721 -> failwith "Unexpected application of incr_depth" in
    let incr_depth_step =
      let uu____1725 =
        FStar_Ident.lid_of_str "FStar.Tactics.Types.incr_depth" in
      {
        FStar_TypeChecker_Normalize.name = uu____1725;
        FStar_TypeChecker_Normalize.arity = (Prims.parse_int "1");
        FStar_TypeChecker_Normalize.strong_reduction_ok = false;
        FStar_TypeChecker_Normalize.requires_binder_substitution = false;
        FStar_TypeChecker_Normalize.interpretation = incr_depth_interp
      } in
    let tracepoint_interp psc args =
      match args with
      | (ps,uu____1742)::[] ->
          let uu____1759 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1759
            (fun ps1  ->
               let ps2 = FStar_Tactics_Types.set_ps_psc psc ps1 in
               FStar_Tactics_Types.tracepoint ps2;
               FStar_Pervasives_Native.Some FStar_Syntax_Util.exp_unit)
      | uu____1772 -> failwith "Unexpected application of tracepoint" in
    let set_proofstate_range_interp psc args =
      match args with
      | (ps,uu____1789)::(r,uu____1791)::[] ->
          let uu____1818 = FStar_Tactics_Embedding.unembed_proofstate ps in
          FStar_Util.bind_opt uu____1818
            (fun ps1  ->
               let uu____1824 = FStar_Syntax_Embeddings.unembed_range r in
               FStar_Util.bind_opt uu____1824
                 (fun r1  ->
                    let ps' = FStar_Tactics_Types.set_proofstate_range ps1 r1 in
                    let uu____1832 =
                      let uu____1833 =
                        FStar_TypeChecker_Normalize.psc_range psc in
                      FStar_Tactics_Embedding.embed_proofstate uu____1833 ps' in
                    FStar_Pervasives_Native.Some uu____1832))
      | uu____1834 ->
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
      let uu___63_1848 = t in
      {
        FStar_Syntax_Syntax.n = (uu___63_1848.FStar_Syntax_Syntax.n);
        FStar_Syntax_Syntax.pos = rng;
        FStar_Syntax_Syntax.vars = (uu___63_1848.FStar_Syntax_Syntax.vars)
      } in
    let get1 t = FStar_Pervasives_Native.Some t in
    let uu____1855 =
      let uu____1858 =
        mktac2 () () () "__fail"
          (fun a433  ->
             fun a434  ->
               (Obj.magic (fun uu____1860  -> FStar_Tactics_Basic.fail)) a433
                 a434) (Obj.magic get1)
          (Obj.magic FStar_Syntax_Embeddings.unembed_string) (Obj.magic put1)
          FStar_Syntax_Syntax.t_unit in
      let uu____1861 =
        let uu____1864 =
          mktac0 () "__trivial" (Obj.magic FStar_Tactics_Basic.trivial)
            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
            FStar_Syntax_Syntax.t_unit in
        let uu____1865 =
          let uu____1868 =
            let uu____1869 =
              FStar_Syntax_Embeddings.embed_option put1
                FStar_Syntax_Syntax.t_unit in
            mktac2 () () () "__trytac"
              (fun a435  ->
                 fun a436  ->
                   (Obj.magic (fun uu____1875  -> FStar_Tactics_Basic.trytac))
                     a435 a436) (Obj.magic get1)
              (Obj.magic (unembed_tactic_0' get1)) (Obj.magic uu____1869)
              FStar_Syntax_Syntax.t_unit in
          let uu____1882 =
            let uu____1885 =
              mktac0 () "__intro" (Obj.magic FStar_Tactics_Basic.intro)
                (Obj.magic FStar_Reflection_Basic.embed_binder)
                FStar_Reflection_Data.fstar_refl_binder in
            let uu____1886 =
              let uu____1889 =
                let uu____1890 =
                  FStar_Syntax_Embeddings.embed_pair
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Basic.embed_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                let uu____1897 =
                  FStar_Tactics_Embedding.pair_typ
                    FStar_Reflection_Data.fstar_refl_binder
                    FStar_Reflection_Data.fstar_refl_binder in
                mktac0 () "__intro_rec"
                  (Obj.magic FStar_Tactics_Basic.intro_rec)
                  (Obj.magic uu____1890) uu____1897 in
              let uu____1904 =
                let uu____1907 =
                  let uu____1908 =
                    FStar_Syntax_Embeddings.unembed_list
                      FStar_Syntax_Embeddings.unembed_norm_step in
                  mktac1 () () "__norm"
                    (fun a437  -> (Obj.magic FStar_Tactics_Basic.norm) a437)
                    (Obj.magic uu____1908)
                    (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                    FStar_Syntax_Syntax.t_unit in
                let uu____1917 =
                  let uu____1920 =
                    let uu____1921 =
                      FStar_Syntax_Embeddings.unembed_list
                        FStar_Syntax_Embeddings.unembed_norm_step in
                    mktac3 () () () () "__norm_term_env"
                      (fun a438  ->
                         fun a439  ->
                           fun a440  ->
                             (Obj.magic FStar_Tactics_Basic.norm_term_env)
                               a438 a439 a440)
                      (Obj.magic FStar_Reflection_Basic.unembed_env)
                      (Obj.magic uu____1921)
                      (Obj.magic FStar_Reflection_Basic.unembed_term)
                      (Obj.magic FStar_Reflection_Basic.embed_term)
                      FStar_Syntax_Syntax.t_term in
                  let uu____1930 =
                    let uu____1933 =
                      let uu____1934 =
                        FStar_Syntax_Embeddings.unembed_list
                          FStar_Syntax_Embeddings.unembed_norm_step in
                      mktac2 () () () "__norm_binder_type"
                        (fun a441  ->
                           fun a442  ->
                             (Obj.magic FStar_Tactics_Basic.norm_binder_type)
                               a441 a442) (Obj.magic uu____1934)
                        (Obj.magic FStar_Reflection_Basic.unembed_binder)
                        (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                        FStar_Syntax_Syntax.t_unit in
                    let uu____1943 =
                      let uu____1946 =
                        mktac2 () () () "__rename_to"
                          (fun a443  ->
                             fun a444  ->
                               (Obj.magic FStar_Tactics_Basic.rename_to) a443
                                 a444)
                          (Obj.magic FStar_Reflection_Basic.unembed_binder)
                          (Obj.magic FStar_Syntax_Embeddings.unembed_string)
                          (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                          FStar_Syntax_Syntax.t_unit in
                      let uu____1947 =
                        let uu____1950 =
                          mktac1 () () "__binder_retype"
                            (fun a445  ->
                               (Obj.magic FStar_Tactics_Basic.binder_retype)
                                 a445)
                            (Obj.magic FStar_Reflection_Basic.unembed_binder)
                            (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                            FStar_Syntax_Syntax.t_unit in
                        let uu____1951 =
                          let uu____1954 =
                            mktac0 () "__revert"
                              (Obj.magic FStar_Tactics_Basic.revert)
                              (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                              FStar_Syntax_Syntax.t_unit in
                          let uu____1955 =
                            let uu____1958 =
                              mktac0 () "__clear_top"
                                (Obj.magic FStar_Tactics_Basic.clear_top)
                                (Obj.magic FStar_Syntax_Embeddings.embed_unit)
                                FStar_Syntax_Syntax.t_unit in
                            let uu____1959 =
                              let uu____1962 =
                                mktac1 () () "__clear"
                                  (fun a446  ->
                                     (Obj.magic FStar_Tactics_Basic.clear)
                                       a446)
                                  (Obj.magic
                                     FStar_Reflection_Basic.unembed_binder)
                                  (Obj.magic
                                     FStar_Syntax_Embeddings.embed_unit)
                                  FStar_Syntax_Syntax.t_unit in
                              let uu____1963 =
                                let uu____1966 =
                                  mktac1 () () "__rewrite"
                                    (fun a447  ->
                                       (Obj.magic FStar_Tactics_Basic.rewrite)
                                         a447)
                                    (Obj.magic
                                       FStar_Reflection_Basic.unembed_binder)
                                    (Obj.magic
                                       FStar_Syntax_Embeddings.embed_unit)
                                    FStar_Syntax_Syntax.t_unit in
                                let uu____1967 =
                                  let uu____1970 =
                                    mktac0 () "__smt"
                                      (Obj.magic FStar_Tactics_Basic.smt)
                                      (Obj.magic
                                         FStar_Syntax_Embeddings.embed_unit)
                                      FStar_Syntax_Syntax.t_unit in
                                  let uu____1971 =
                                    let uu____1974 =
                                      mktac0 () "__refine_intro"
                                        (Obj.magic
                                           FStar_Tactics_Basic.refine_intro)
                                        (Obj.magic
                                           FStar_Syntax_Embeddings.embed_unit)
                                        FStar_Syntax_Syntax.t_unit in
                                    let uu____1975 =
                                      let uu____1978 =
                                        mktac3 () () () () "__t_exact"
                                          (fun a448  ->
                                             fun a449  ->
                                               fun a450  ->
                                                 (Obj.magic
                                                    FStar_Tactics_Basic.t_exact)
                                                   a448 a449 a450)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.unembed_bool)
                                          (Obj.magic
                                             FStar_Reflection_Basic.unembed_term)
                                          (Obj.magic
                                             FStar_Syntax_Embeddings.embed_unit)
                                          FStar_Syntax_Syntax.t_unit in
                                      let uu____1979 =
                                        let uu____1982 =
                                          mktac1 () () "__apply"
                                            (fun a451  ->
                                               (Obj.magic
                                                  (FStar_Tactics_Basic.apply
                                                     true)) a451)
                                            (Obj.magic
                                               FStar_Reflection_Basic.unembed_term)
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_unit)
                                            FStar_Syntax_Syntax.t_unit in
                                        let uu____1983 =
                                          let uu____1986 =
                                            mktac1 () () "__apply_raw"
                                              (fun a452  ->
                                                 (Obj.magic
                                                    (FStar_Tactics_Basic.apply
                                                       false)) a452)
                                              (Obj.magic
                                                 FStar_Reflection_Basic.unembed_term)
                                              (Obj.magic
                                                 FStar_Syntax_Embeddings.embed_unit)
                                              FStar_Syntax_Syntax.t_unit in
                                          let uu____1987 =
                                            let uu____1990 =
                                              mktac1 () () "__apply_lemma"
                                                (fun a453  ->
                                                   (Obj.magic
                                                      FStar_Tactics_Basic.apply_lemma)
                                                     a453)
                                                (Obj.magic
                                                   FStar_Reflection_Basic.unembed_term)
                                                (Obj.magic
                                                   FStar_Syntax_Embeddings.embed_unit)
                                                FStar_Syntax_Syntax.t_unit in
                                            let uu____1991 =
                                              let uu____1994 =
                                                let uu____1995 =
                                                  FStar_Syntax_Embeddings.embed_pair
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit
                                                    put1
                                                    FStar_Syntax_Syntax.t_unit in
                                                mktac5 () () () () () ()
                                                  "__divide"
                                                  (fun a454  ->
                                                     fun a455  ->
                                                       fun a456  ->
                                                         fun a457  ->
                                                           fun a458  ->
                                                             (Obj.magic
                                                                (fun
                                                                   uu____2004
                                                                    ->
                                                                   fun
                                                                    uu____2005
                                                                     ->
                                                                    FStar_Tactics_Basic.divide))
                                                               a454 a455 a456
                                                               a457 a458)
                                                  (Obj.magic get1)
                                                  (Obj.magic get1)
                                                  (Obj.magic
                                                     FStar_Syntax_Embeddings.unembed_int)
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic
                                                     (unembed_tactic_0' get1))
                                                  (Obj.magic uu____1995)
                                                  FStar_Syntax_Syntax.t_unit in
                                              let uu____2012 =
                                                let uu____2015 =
                                                  mktac1 () ()
                                                    "__set_options"
                                                    (fun a459  ->
                                                       (Obj.magic
                                                          FStar_Tactics_Basic.set_options)
                                                         a459)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.unembed_string)
                                                    (Obj.magic
                                                       FStar_Syntax_Embeddings.embed_unit)
                                                    FStar_Syntax_Syntax.t_unit in
                                                let uu____2016 =
                                                  let uu____2019 =
                                                    mktac2 () () () "__seq"
                                                      (fun a460  ->
                                                         fun a461  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.seq)
                                                             a460 a461)
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         (unembed_tactic_0'
                                                            FStar_Syntax_Embeddings.unembed_unit))
                                                      (Obj.magic
                                                         FStar_Syntax_Embeddings.embed_unit)
                                                      FStar_Syntax_Syntax.t_unit in
                                                  let uu____2020 =
                                                    let uu____2023 =
                                                      mktac1 () () "__tc"
                                                        (fun a462  ->
                                                           (Obj.magic
                                                              FStar_Tactics_Basic.tc)
                                                             a462)
                                                        (Obj.magic
                                                           FStar_Reflection_Basic.unembed_term)
                                                        (Obj.magic
                                                           FStar_Reflection_Basic.embed_term)
                                                        FStar_Syntax_Syntax.t_term in
                                                    let uu____2024 =
                                                      let uu____2027 =
                                                        mktac1 () ()
                                                          "__unshelve"
                                                          (fun a463  ->
                                                             (Obj.magic
                                                                FStar_Tactics_Basic.unshelve)
                                                               a463)
                                                          (Obj.magic
                                                             FStar_Reflection_Basic.unembed_term)
                                                          (Obj.magic
                                                             FStar_Syntax_Embeddings.embed_unit)
                                                          FStar_Syntax_Syntax.t_unit in
                                                      let uu____2028 =
                                                        let uu____2031 =
                                                          mktac2 () () ()
                                                            "__unquote"
                                                            (fun a464  ->
                                                               fun a465  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.unquote)
                                                                   a464 a465)
                                                            (Obj.magic get1)
                                                            (Obj.magic
                                                               FStar_Reflection_Basic.unembed_term)
                                                            (Obj.magic put1)
                                                            FStar_Syntax_Syntax.t_unit in
                                                        let uu____2032 =
                                                          let uu____2035 =
                                                            mktac1 () ()
                                                              "__prune"
                                                              (fun a466  ->
                                                                 (Obj.magic
                                                                    FStar_Tactics_Basic.prune)
                                                                   a466)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.unembed_string)
                                                              (Obj.magic
                                                                 FStar_Syntax_Embeddings.embed_unit)
                                                              FStar_Syntax_Syntax.t_unit in
                                                          let uu____2036 =
                                                            let uu____2039 =
                                                              mktac1 () ()
                                                                "__addns"
                                                                (fun a467  ->
                                                                   (Obj.magic
                                                                    FStar_Tactics_Basic.addns)
                                                                    a467)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_string)
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.embed_unit)
                                                                FStar_Syntax_Syntax.t_unit in
                                                            let uu____2040 =
                                                              let uu____2043
                                                                =
                                                                mktac1 () ()
                                                                  "__print"
                                                                  (fun a468 
                                                                    ->
                                                                    (Obj.magic
                                                                    (fun x 
                                                                    ->
                                                                    FStar_Tactics_Basic.tacprint
                                                                    x;
                                                                    FStar_Tactics_Basic.ret
                                                                    ())) a468)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                  (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                  FStar_Syntax_Syntax.t_unit in
                                                              let uu____2048
                                                                =
                                                                let uu____2051
                                                                  =
                                                                  mktac1 ()
                                                                    ()
                                                                    "__dump"
                                                                    (
                                                                    fun a469 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state)
                                                                    a469)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (
                                                                    Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                let uu____2052
                                                                  =
                                                                  let uu____2055
                                                                    =
                                                                    mktac1 ()
                                                                    ()
                                                                    "__dump1"
                                                                    (fun a470
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.print_proof_state1)
                                                                    a470)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                  let uu____2056
                                                                    =
                                                                    let uu____2059
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__pointwise"
                                                                    (fun a471
                                                                     ->
                                                                    fun a472 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.pointwise)
                                                                    a471 a472)
                                                                    (Obj.magic
                                                                    FStar_Tactics_Embedding.unembed_direction)
                                                                    (Obj.magic
                                                                    (unembed_tactic_0'
                                                                    FStar_Syntax_Embeddings.unembed_unit))
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2060
                                                                    =
                                                                    let uu____2063
                                                                    =
                                                                    mktac0 ()
                                                                    "__trefl"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.trefl)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2064
                                                                    =
                                                                    let uu____2067
                                                                    =
                                                                    mktac0 ()
                                                                    "__later"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.later)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2068
                                                                    =
                                                                    let uu____2071
                                                                    =
                                                                    mktac0 ()
                                                                    "__dup"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.dup)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2072
                                                                    =
                                                                    let uu____2075
                                                                    =
                                                                    mktac0 ()
                                                                    "__flip"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.flip)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2076
                                                                    =
                                                                    let uu____2079
                                                                    =
                                                                    mktac0 ()
                                                                    "__qed"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.qed)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_unit)
                                                                    FStar_Syntax_Syntax.t_unit in
                                                                    let uu____2080
                                                                    =
                                                                    let uu____2083
                                                                    =
                                                                    let uu____2084
                                                                    =
                                                                    FStar_Syntax_Embeddings.embed_pair
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Reflection_Basic.embed_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2091
                                                                    =
                                                                    FStar_Tactics_Embedding.pair_typ
                                                                    FStar_Syntax_Syntax.t_term
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    mktac1 ()
                                                                    ()
                                                                    "__cases"
                                                                    (fun a473
                                                                     ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cases)
                                                                    a473)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    uu____2084)
                                                                    uu____2091 in
                                                                    let uu____2098
                                                                    =
                                                                    let uu____2101
                                                                    =
                                                                    mktac0 ()
                                                                    "__top_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.top_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2102
                                                                    =
                                                                    let uu____2105
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_env"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_env)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_env)
                                                                    FStar_Reflection_Data.fstar_refl_env in
                                                                    let uu____2106
                                                                    =
                                                                    let uu____2109
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_goal"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_goal')
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2110
                                                                    =
                                                                    let uu____2113
                                                                    =
                                                                    mktac0 ()
                                                                    "__cur_witness"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.cur_witness)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2114
                                                                    =
                                                                    let uu____2117
                                                                    =
                                                                    mktac0 ()
                                                                    "__is_guard"
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.is_guard)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2118
                                                                    =
                                                                    let uu____2121
                                                                    =
                                                                    let uu____2122
                                                                    =
                                                                    FStar_Syntax_Embeddings.unembed_option
                                                                    FStar_Reflection_Basic.unembed_term in
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__uvar_env"
                                                                    (fun a474
                                                                     ->
                                                                    fun a475 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.uvar_env)
                                                                    a474 a475)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_env)
                                                                    (Obj.magic
                                                                    uu____2122)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.embed_term)
                                                                    FStar_Syntax_Syntax.t_term in
                                                                    let uu____2131
                                                                    =
                                                                    let uu____2134
                                                                    =
                                                                    mktac2 ()
                                                                    () ()
                                                                    "__unify"
                                                                    (fun a476
                                                                     ->
                                                                    fun a477 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.unify)
                                                                    a476 a477)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Reflection_Basic.unembed_term)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_bool)
                                                                    FStar_Syntax_Syntax.t_bool in
                                                                    let uu____2135
                                                                    =
                                                                    let uu____2138
                                                                    =
                                                                    mktac3 ()
                                                                    () () ()
                                                                    "__launch_process"
                                                                    (fun a478
                                                                     ->
                                                                    fun a479 
                                                                    ->
                                                                    fun a480 
                                                                    ->
                                                                    (Obj.magic
                                                                    FStar_Tactics_Basic.launch_process)
                                                                    a478 a479
                                                                    a480)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.unembed_string)
                                                                    (Obj.magic
                                                                    FStar_Syntax_Embeddings.embed_string)
                                                                    FStar_Syntax_Syntax.t_string in
                                                                    [uu____2138;
                                                                    decr_depth_step;
                                                                    incr_depth_step;
                                                                    tracepoint_step;
                                                                    set_proofstate_range_step] in
                                                                    uu____2134
                                                                    ::
                                                                    uu____2135 in
                                                                    uu____2121
                                                                    ::
                                                                    uu____2131 in
                                                                    uu____2117
                                                                    ::
                                                                    uu____2118 in
                                                                    uu____2113
                                                                    ::
                                                                    uu____2114 in
                                                                    uu____2109
                                                                    ::
                                                                    uu____2110 in
                                                                    uu____2105
                                                                    ::
                                                                    uu____2106 in
                                                                    uu____2101
                                                                    ::
                                                                    uu____2102 in
                                                                    uu____2083
                                                                    ::
                                                                    uu____2098 in
                                                                    uu____2079
                                                                    ::
                                                                    uu____2080 in
                                                                    uu____2075
                                                                    ::
                                                                    uu____2076 in
                                                                    uu____2071
                                                                    ::
                                                                    uu____2072 in
                                                                    uu____2067
                                                                    ::
                                                                    uu____2068 in
                                                                    uu____2063
                                                                    ::
                                                                    uu____2064 in
                                                                    uu____2059
                                                                    ::
                                                                    uu____2060 in
                                                                  uu____2055
                                                                    ::
                                                                    uu____2056 in
                                                                uu____2051 ::
                                                                  uu____2052 in
                                                              uu____2043 ::
                                                                uu____2048 in
                                                            uu____2039 ::
                                                              uu____2040 in
                                                          uu____2035 ::
                                                            uu____2036 in
                                                        uu____2031 ::
                                                          uu____2032 in
                                                      uu____2027 ::
                                                        uu____2028 in
                                                    uu____2023 :: uu____2024 in
                                                  uu____2019 :: uu____2020 in
                                                uu____2015 :: uu____2016 in
                                              uu____1994 :: uu____2012 in
                                            uu____1990 :: uu____1991 in
                                          uu____1986 :: uu____1987 in
                                        uu____1982 :: uu____1983 in
                                      uu____1978 :: uu____1979 in
                                    uu____1974 :: uu____1975 in
                                  uu____1970 :: uu____1971 in
                                uu____1966 :: uu____1967 in
                              uu____1962 :: uu____1963 in
                            uu____1958 :: uu____1959 in
                          uu____1954 :: uu____1955 in
                        uu____1950 :: uu____1951 in
                      uu____1946 :: uu____1947 in
                    uu____1933 :: uu____1943 in
                  uu____1920 :: uu____1930 in
                uu____1907 :: uu____1917 in
              uu____1889 :: uu____1904 in
            uu____1885 :: uu____1886 in
          uu____1868 :: uu____1882 in
        uu____1864 :: uu____1865 in
      uu____1858 :: uu____1861 in
    FStar_List.append uu____1855
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
             let uu____2161 =
               let uu____2162 =
                 let uu____2163 =
                   let uu____2164 =
                     FStar_Tactics_Embedding.embed_proofstate rng proof_state in
                   FStar_Syntax_Syntax.as_arg uu____2164 in
                 [uu____2163] in
               FStar_Syntax_Syntax.mk_Tm_app embedded_tac_b uu____2162 in
             uu____2161 FStar_Pervasives_Native.None rng in
           let steps =
             [FStar_TypeChecker_Normalize.Weak;
             FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldUntil
               FStar_Syntax_Syntax.Delta_constant;
             FStar_TypeChecker_Normalize.UnfoldTac;
             FStar_TypeChecker_Normalize.Primops] in
           (let uu____2171 = FStar_ST.op_Bang tacdbg in
            if uu____2171
            then
              let uu____2191 = FStar_Syntax_Print.term_to_string tm in
              FStar_Util.print1 "Starting normalizer with %s\n" uu____2191
            else ());
           (let result =
              let uu____2194 = primitive_steps () in
              FStar_TypeChecker_Normalize.normalize_with_primitive_steps
                uu____2194 steps proof_state.FStar_Tactics_Types.main_context
                tm in
            (let uu____2198 = FStar_ST.op_Bang tacdbg in
             if uu____2198
             then
               let uu____2218 = FStar_Syntax_Print.term_to_string result in
               FStar_Util.print1 "Reduced tactic: got %s\n" uu____2218
             else ());
            (let uu____2220 =
               FStar_Tactics_Embedding.unembed_result result unembed_b in
             match uu____2220 with
             | FStar_Pervasives_Native.Some (FStar_Util.Inl (b,ps)) ->
                 let uu____2263 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2263
                   (fun uu____2267  -> FStar_Tactics_Basic.ret b)
             | FStar_Pervasives_Native.Some (FStar_Util.Inr (msg,ps)) ->
                 let uu____2290 = FStar_Tactics_Basic.set ps in
                 FStar_Tactics_Basic.bind uu____2290
                   (fun uu____2294  -> FStar_Tactics_Basic.fail msg)
             | FStar_Pervasives_Native.None  ->
                 let uu____2307 =
                   let uu____2312 =
                     let uu____2313 =
                       FStar_Syntax_Print.term_to_string result in
                     FStar_Util.format1
                       "Tactic got stuck! Please file a bug report with a minimal reproduction of this issue.\n%s"
                       uu____2313 in
                   (FStar_Errors.Fatal_TacticGotStuck, uu____2312) in
                 FStar_Errors.raise_error uu____2307
                   (proof_state.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.range)))
and unembed_tactic_0':
  'Ab .
    'Ab FStar_Syntax_Embeddings.unembedder ->
      FStar_Syntax_Syntax.term ->
        'Ab FStar_Tactics_Basic.tac FStar_Pervasives_Native.option
  =
  fun unembed_b  ->
    fun embedded_tac_b  ->
      let uu____2322 = unembed_tactic_0 unembed_b embedded_tac_b in
      FStar_All.pipe_left (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
        uu____2322
let report_implicits:
  FStar_Tactics_Types.proofstate ->
    FStar_TypeChecker_Env.implicits -> Prims.unit
  =
  fun ps  ->
    fun is  ->
      let errs =
        FStar_List.map
          (fun uu____2378  ->
             match uu____2378 with
             | (r,uu____2398,uv,uu____2400,ty,rng) ->
                 let uu____2403 =
                   let uu____2404 = FStar_Syntax_Print.uvar_to_string uv in
                   let uu____2405 = FStar_Syntax_Print.term_to_string ty in
                   FStar_Util.format3
                     "Tactic left uninstantiated unification variable %s of type %s (reason = \"%s\")"
                     uu____2404 uu____2405 r in
                 (FStar_Errors.Fatal_UninstantiatedUnificationVarInTactic,
                   uu____2403, rng)) is in
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
        (let uu____2454 = FStar_ST.op_Bang tacdbg in
         if uu____2454
         then
           let uu____2474 = FStar_Syntax_Print.term_to_string tactic in
           FStar_Util.print1 "About to reduce uvars on: %s\n" uu____2474
         else ());
        (let tactic1 =
           FStar_TypeChecker_Normalize.reduce_uvar_solutions env tactic in
         FStar_Errors.stop_if_err ();
         (let tau =
            unembed_tactic_0 FStar_Syntax_Embeddings.unembed_unit tactic1 in
          let uu____2481 = FStar_TypeChecker_Env.clear_expected_typ env in
          match uu____2481 with
          | (env1,uu____2495) ->
              let env2 =
                let uu___64_2501 = env1 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___64_2501.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___64_2501.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___64_2501.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___64_2501.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___64_2501.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___64_2501.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___64_2501.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___64_2501.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___64_2501.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp = false;
                  FStar_TypeChecker_Env.effects =
                    (uu___64_2501.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___64_2501.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___64_2501.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___64_2501.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___64_2501.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___64_2501.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___64_2501.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___64_2501.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___64_2501.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___64_2501.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.failhard =
                    (uu___64_2501.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___64_2501.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___64_2501.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___64_2501.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___64_2501.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___64_2501.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qname_and_index =
                    (uu___64_2501.FStar_TypeChecker_Env.qname_and_index);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___64_2501.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth =
                    (uu___64_2501.FStar_TypeChecker_Env.synth);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___64_2501.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___64_2501.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___64_2501.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv =
                    (uu___64_2501.FStar_TypeChecker_Env.dsenv);
                  FStar_TypeChecker_Env.dep_graph =
                    (uu___64_2501.FStar_TypeChecker_Env.dep_graph)
                } in
              let uu____2502 =
                FStar_Tactics_Basic.proofstate_of_goal_ty env2 typ in
              (match uu____2502 with
               | (ps,w) ->
                   ((let uu____2516 = FStar_ST.op_Bang tacdbg in
                     if uu____2516
                     then
                       let uu____2536 = FStar_Syntax_Print.term_to_string typ in
                       FStar_Util.print1 "Running tactic with goal = %s\n"
                         uu____2536
                     else ());
                    (let uu____2538 = FStar_Tactics_Basic.run tau ps in
                     match uu____2538 with
                     | FStar_Tactics_Result.Success (uu____2547,ps1) ->
                         ((let uu____2550 = FStar_ST.op_Bang tacdbg in
                           if uu____2550
                           then
                             let uu____2570 =
                               FStar_Syntax_Print.term_to_string w in
                             FStar_Util.print1
                               "Tactic generated proofterm %s\n" uu____2570
                           else ());
                          FStar_List.iter
                            (fun g  ->
                               let uu____2577 =
                                 FStar_Tactics_Basic.is_irrelevant g in
                               if uu____2577
                               then
                                 let uu____2578 =
                                   FStar_TypeChecker_Rel.teq_nosmt
                                     g.FStar_Tactics_Types.context
                                     g.FStar_Tactics_Types.witness
                                     FStar_Syntax_Util.exp_unit in
                                 (if uu____2578
                                  then ()
                                  else
                                    (let uu____2580 =
                                       let uu____2581 =
                                         FStar_Syntax_Print.term_to_string
                                           g.FStar_Tactics_Types.witness in
                                       FStar_Util.format1
                                         "Irrelevant tactic witness does not unify with (): %s"
                                         uu____2581 in
                                     failwith uu____2580))
                               else ())
                            (FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals);
                          (let g =
                             let uu___65_2584 =
                               FStar_TypeChecker_Rel.trivial_guard in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___65_2584.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___65_2584.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (uu___65_2584.FStar_TypeChecker_Env.univ_ineqs);
                               FStar_TypeChecker_Env.implicits =
                                 (ps1.FStar_Tactics_Types.all_implicits)
                             } in
                           let g1 =
                             let uu____2586 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g in
                             FStar_All.pipe_right uu____2586
                               FStar_TypeChecker_Rel.resolve_implicits_tac in
                           report_implicits ps1
                             g1.FStar_TypeChecker_Env.implicits;
                           ((FStar_List.append ps1.FStar_Tactics_Types.goals
                               ps1.FStar_Tactics_Types.smt_goals), w)))
                     | FStar_Tactics_Result.Failed (s,ps1) ->
                         ((let uu____2593 =
                             let uu____2594 =
                               FStar_TypeChecker_Normalize.psc_subst
                                 ps1.FStar_Tactics_Types.psc in
                             FStar_Tactics_Types.subst_proof_state uu____2594
                               ps1 in
                           FStar_Tactics_Basic.dump_proofstate uu____2593
                             "at the time of failure");
                          (let uu____2595 =
                             let uu____2600 =
                               FStar_Util.format1 "user tactic failed: %s" s in
                             (FStar_Errors.Fatal_ArgumentLengthMismatch,
                               uu____2600) in
                           FStar_Errors.raise_error uu____2595
                             typ.FStar_Syntax_Syntax.pos)))))))
type pol =
  | Pos
  | Neg
  | Both[@@deriving show]
let uu___is_Pos: pol -> Prims.bool =
  fun projectee  -> match projectee with | Pos  -> true | uu____2610 -> false
let uu___is_Neg: pol -> Prims.bool =
  fun projectee  -> match projectee with | Neg  -> true | uu____2614 -> false
let uu___is_Both: pol -> Prims.bool =
  fun projectee  ->
    match projectee with | Both  -> true | uu____2618 -> false
type 'a tres_m =
  | Unchanged of 'a
  | Simplified of ('a,FStar_Tactics_Types.goal Prims.list)
  FStar_Pervasives_Native.tuple2
  | Dual of ('a,'a,FStar_Tactics_Types.goal Prims.list)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_Unchanged: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Unchanged _0 -> true | uu____2667 -> false
let __proj__Unchanged__item___0: 'a . 'a tres_m -> 'a =
  fun projectee  -> match projectee with | Unchanged _0 -> _0
let uu___is_Simplified: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplified _0 -> true | uu____2703 -> false
let __proj__Simplified__item___0:
  'a .
    'a tres_m ->
      ('a,FStar_Tactics_Types.goal Prims.list) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Simplified _0 -> _0
let uu___is_Dual: 'a . 'a tres_m -> Prims.bool =
  fun projectee  ->
    match projectee with | Dual _0 -> true | uu____2753 -> false
let __proj__Dual__item___0:
  'a .
    'a tres_m ->
      ('a,'a,FStar_Tactics_Types.goal Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Dual _0 -> _0
type tres = FStar_Syntax_Syntax.term tres_m[@@deriving show]
let tpure: 'Auu____2791 . 'Auu____2791 -> 'Auu____2791 tres_m =
  fun x  -> Unchanged x
let flip: pol -> pol =
  fun p  -> match p with | Pos  -> Neg | Neg  -> Pos | Both  -> Both
let by_tactic_interp:
  pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres =
  fun pol  ->
    fun e  ->
      fun t  ->
        let uu____2810 = FStar_Syntax_Util.head_and_args t in
        match uu____2810 with
        | (hd1,args) ->
            let uu____2847 =
              let uu____2860 =
                let uu____2861 = FStar_Syntax_Util.un_uinst hd1 in
                uu____2861.FStar_Syntax_Syntax.n in
              (uu____2860, args) in
            (match uu____2847 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(rett,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____2874))::(tactic,FStar_Pervasives_Native.None
                                                                 )::(assertion,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.by_tactic_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____2937 = run_tactic_on_typ tactic e assertion in
                      (match uu____2937 with
                       | (gs,uu____2945) ->
                           Simplified (FStar_Syntax_Util.t_true, gs))
                  | Both  ->
                      let uu____2952 = run_tactic_on_typ tactic e assertion in
                      (match uu____2952 with
                       | (gs,uu____2960) ->
                           Dual (assertion, FStar_Syntax_Util.t_true, gs))
                  | Neg  -> Simplified (assertion, []))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(assertion,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.spinoff_lid
                 ->
                 (match pol with
                  | Pos  ->
                      let uu____3011 =
                        let uu____3018 =
                          let uu____3021 =
                            let uu____3022 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3022 in
                          [uu____3021] in
                        (FStar_Syntax_Util.t_true, uu____3018) in
                      Simplified uu____3011
                  | Both  ->
                      let uu____3033 =
                        let uu____3046 =
                          let uu____3049 =
                            let uu____3050 =
                              FStar_Tactics_Basic.goal_of_goal_ty e assertion in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____3050 in
                          [uu____3049] in
                        (assertion, FStar_Syntax_Util.t_true, uu____3046) in
                      Dual uu____3033
                  | Neg  -> Simplified (assertion, []))
             | uu____3071 -> Unchanged t)
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
    fun uu___62_3151  ->
      match uu___62_3151 with
      | Unchanged t -> let uu____3157 = f t in Unchanged uu____3157
      | Simplified (t,gs) ->
          let uu____3164 = let uu____3171 = f t in (uu____3171, gs) in
          Simplified uu____3164
      | Dual (tn,tp,gs) ->
          let uu____3181 =
            let uu____3190 = f tn in
            let uu____3191 = f tp in (uu____3190, uu____3191, gs) in
          Dual uu____3181
let comb2: 'a 'b 'c . ('a -> 'b -> 'c) -> 'a tres_m -> 'b tres_m -> 'c tres_m
  =
  fun f  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (Unchanged t1,Unchanged t2) ->
            let uu____3245 = f t1 t2 in Unchanged uu____3245
        | (Unchanged t1,Simplified (t2,gs)) ->
            let uu____3257 = let uu____3264 = f t1 t2 in (uu____3264, gs) in
            Simplified uu____3257
        | (Simplified (t1,gs),Unchanged t2) ->
            let uu____3278 = let uu____3285 = f t1 t2 in (uu____3285, gs) in
            Simplified uu____3278
        | (Simplified (t1,gs1),Simplified (t2,gs2)) ->
            let uu____3304 =
              let uu____3311 = f t1 t2 in
              (uu____3311, (FStar_List.append gs1 gs2)) in
            Simplified uu____3304
        | uu____3314 ->
            let uu____3323 = explode x in
            (match uu____3323 with
             | (n1,p1,gs1) ->
                 let uu____3341 = explode y in
                 (match uu____3341 with
                  | (n2,p2,gs2) ->
                      let uu____3359 =
                        let uu____3368 = f n1 n2 in
                        let uu____3369 = f p1 p2 in
                        (uu____3368, uu____3369, (FStar_List.append gs1 gs2)) in
                      Dual uu____3359))
let comb_list: 'a . 'a tres_m Prims.list -> 'a Prims.list tres_m =
  fun rs  ->
    let rec aux rs1 acc =
      match rs1 with
      | [] -> acc
      | hd1::tl1 ->
          let uu____3434 = comb2 (fun l  -> fun r  -> l :: r) hd1 acc in
          aux tl1 uu____3434 in
    aux (FStar_List.rev rs) (tpure [])
let emit: 'a . FStar_Tactics_Types.goal Prims.list -> 'a tres_m -> 'a tres_m
  =
  fun gs  ->
    fun m  -> comb2 (fun uu____3477  -> fun x  -> x) (Simplified ((), gs)) m
let rec traverse:
  (pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres) ->
    pol -> FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> tres
  =
  fun f  ->
    fun pol  ->
      fun e  ->
        fun t  ->
          let r =
            let uu____3511 =
              let uu____3512 = FStar_Syntax_Subst.compress t in
              uu____3512.FStar_Syntax_Syntax.n in
            match uu____3511 with
            | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
                let tr = traverse f pol e t1 in
                let uu____3524 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_uinst (t', us)) in
                uu____3524 tr
            | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
                let tr = traverse f pol e t1 in
                let uu____3548 =
                  comb1 (fun t'  -> FStar_Syntax_Syntax.Tm_meta (t', m)) in
                uu____3548 tr
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3566;
                   FStar_Syntax_Syntax.vars = uu____3567;_},(p,uu____3569)::
                 (q,uu____3571)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid
                ->
                let x =
                  let uu____3611 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3611 in
                let r1 = traverse f (flip pol) e p in
                let r2 =
                  let uu____3614 = FStar_TypeChecker_Env.push_bv e x in
                  traverse f pol uu____3614 q in
                comb2
                  (fun l  ->
                     fun r  ->
                       let uu____3620 = FStar_Syntax_Util.mk_imp l r in
                       uu____3620.FStar_Syntax_Syntax.n) r1 r2
            | FStar_Syntax_Syntax.Tm_app
                ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.pos = uu____3624;
                   FStar_Syntax_Syntax.vars = uu____3625;_},(p,uu____3627)::
                 (q,uu____3629)::[])
                when
                FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid
                ->
                let xp =
                  let uu____3669 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero p in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3669 in
                let xq =
                  let uu____3671 =
                    FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero q in
                  FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                    uu____3671 in
                let r1 =
                  let uu____3673 = FStar_TypeChecker_Env.push_bv e xq in
                  traverse f Both uu____3673 p in
                let r2 =
                  let uu____3675 = FStar_TypeChecker_Env.push_bv e xp in
                  traverse f Both uu____3675 q in
                (match (r1, r2) with
                 | (Unchanged uu____3678,Unchanged uu____3679) ->
                     comb2
                       (fun l  ->
                          fun r  ->
                            let uu____3689 = FStar_Syntax_Util.mk_iff l r in
                            uu____3689.FStar_Syntax_Syntax.n) r1 r2
                 | uu____3692 ->
                     let uu____3697 = explode r1 in
                     (match uu____3697 with
                      | (pn,pp,gs1) ->
                          let uu____3715 = explode r2 in
                          (match uu____3715 with
                           | (qn,qp,gs2) ->
                               let t1 =
                                 let uu____3736 =
                                   FStar_Syntax_Util.mk_imp pn qp in
                                 let uu____3737 =
                                   FStar_Syntax_Util.mk_imp qn pp in
                                 FStar_Syntax_Util.mk_conj uu____3736
                                   uu____3737 in
                               Simplified
                                 ((t1.FStar_Syntax_Syntax.n),
                                   (FStar_List.append gs1 gs2)))))
            | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                let r0 = traverse f pol e hd1 in
                let r1 =
                  FStar_List.fold_right
                    (fun uu____3789  ->
                       fun r  ->
                         match uu____3789 with
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
                let uu____3907 = FStar_Syntax_Subst.open_term bs t1 in
                (match uu____3907 with
                 | (bs1,topen) ->
                     let e' = FStar_TypeChecker_Env.push_binders e bs1 in
                     let r0 =
                       FStar_List.map
                         (fun uu____3941  ->
                            match uu____3941 with
                            | (bv,aq) ->
                                let r =
                                  traverse f (flip pol) e
                                    bv.FStar_Syntax_Syntax.sort in
                                let uu____3955 =
                                  comb1
                                    (fun s'  ->
                                       ((let uu___66_3979 = bv in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___66_3979.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___66_3979.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort = s'
                                         }), aq)) in
                                uu____3955 r) bs1 in
                     let rbs = comb_list r0 in
                     let rt = traverse f pol e' topen in
                     comb2
                       (fun bs2  ->
                          fun t2  ->
                            let uu____3999 = FStar_Syntax_Util.abs bs2 t2 k in
                            uu____3999.FStar_Syntax_Syntax.n) rbs rt)
            | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,ef) ->
                let uu____4045 = traverse f pol e t1 in
                let uu____4050 =
                  comb1
                    (fun t2  -> FStar_Syntax_Syntax.Tm_ascribed (t2, asc, ef)) in
                uu____4050 uu____4045
            | x -> tpure x in
          match r with
          | Unchanged tn' ->
              f pol e
                (let uu___67_4088 = t in
                 {
                   FStar_Syntax_Syntax.n = tn';
                   FStar_Syntax_Syntax.pos =
                     (uu___67_4088.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___67_4088.FStar_Syntax_Syntax.vars)
                 })
          | Simplified (tn',gs) ->
              let uu____4095 =
                f pol e
                  (let uu___68_4099 = t in
                   {
                     FStar_Syntax_Syntax.n = tn';
                     FStar_Syntax_Syntax.pos =
                       (uu___68_4099.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___68_4099.FStar_Syntax_Syntax.vars)
                   }) in
              emit gs uu____4095
          | Dual (tn,tp,gs) ->
              let rp =
                f pol e
                  (let uu___69_4109 = t in
                   {
                     FStar_Syntax_Syntax.n = tp;
                     FStar_Syntax_Syntax.pos =
                       (uu___69_4109.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___69_4109.FStar_Syntax_Syntax.vars)
                   }) in
              let uu____4110 = explode rp in
              (match uu____4110 with
               | (uu____4119,p',gs') ->
                   Dual
                     ((let uu___70_4133 = t in
                       {
                         FStar_Syntax_Syntax.n = tn;
                         FStar_Syntax_Syntax.pos =
                           (uu___70_4133.FStar_Syntax_Syntax.pos);
                         FStar_Syntax_Syntax.vars =
                           (uu___70_4133.FStar_Syntax_Syntax.vars)
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
      (let uu____4168 =
         FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
       FStar_ST.op_Colon_Equals tacdbg uu____4168);
      (let uu____4189 = FStar_ST.op_Bang tacdbg in
       if uu____4189
       then
         let uu____4209 =
           let uu____4210 = FStar_TypeChecker_Env.all_binders env in
           FStar_All.pipe_right uu____4210
             (FStar_Syntax_Print.binders_to_string ",") in
         let uu____4211 = FStar_Syntax_Print.term_to_string goal in
         FStar_Util.print2 "About to preprocess %s |= %s\n" uu____4209
           uu____4211
       else ());
      (let initial = ((Prims.parse_int "1"), []) in
       let uu____4240 =
         let uu____4247 = traverse by_tactic_interp Pos env goal in
         match uu____4247 with
         | Unchanged t' -> (t', [])
         | Simplified (t',gs) -> (t', gs)
         | uu____4265 -> failwith "no" in
       match uu____4240 with
       | (t',gs) ->
           ((let uu____4287 = FStar_ST.op_Bang tacdbg in
             if uu____4287
             then
               let uu____4307 =
                 let uu____4308 = FStar_TypeChecker_Env.all_binders env in
                 FStar_All.pipe_right uu____4308
                   (FStar_Syntax_Print.binders_to_string ", ") in
               let uu____4309 = FStar_Syntax_Print.term_to_string t' in
               FStar_Util.print2 "Main goal simplified to: %s |- %s\n"
                 uu____4307 uu____4309
             else ());
            (let s = initial in
             let s1 =
               FStar_List.fold_left
                 (fun uu____4356  ->
                    fun g  ->
                      match uu____4356 with
                      | (n1,gs1) ->
                          let phi =
                            let uu____4401 =
                              getprop g.FStar_Tactics_Types.context
                                g.FStar_Tactics_Types.goal_ty in
                            match uu____4401 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____4404 =
                                  let uu____4405 =
                                    FStar_Syntax_Print.term_to_string
                                      g.FStar_Tactics_Types.goal_ty in
                                  FStar_Util.format1
                                    "Tactic returned proof-relevant goal: %s"
                                    uu____4405 in
                                failwith uu____4404
                            | FStar_Pervasives_Native.Some phi -> phi in
                          ((let uu____4408 = FStar_ST.op_Bang tacdbg in
                            if uu____4408
                            then
                              let uu____4428 = FStar_Util.string_of_int n1 in
                              let uu____4429 =
                                FStar_Tactics_Basic.goal_to_string g in
                              FStar_Util.print2 "Got goal #%s: %s\n"
                                uu____4428 uu____4429
                            else ());
                           (let gt' =
                              let uu____4432 =
                                let uu____4433 = FStar_Util.string_of_int n1 in
                                Prims.strcat "Could not prove goal #"
                                  uu____4433 in
                              FStar_TypeChecker_Util.label uu____4432
                                goal.FStar_Syntax_Syntax.pos phi in
                            ((n1 + (Prims.parse_int "1")),
                              (((g.FStar_Tactics_Types.context), gt',
                                 (g.FStar_Tactics_Types.opts)) :: gs1))))) s
                 gs in
             let uu____4448 = s1 in
             match uu____4448 with
             | (uu____4469,gs1) ->
                 let uu____4487 =
                   let uu____4494 = FStar_Options.peek () in
                   (env, t', uu____4494) in
                 uu____4487 :: gs1)))
let reify_tactic: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun a  ->
    let r =
      let uu____4505 =
        let uu____4506 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reify_tactic_lid
            FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____4506 in
      FStar_Syntax_Syntax.mk_Tm_uinst uu____4505 [FStar_Syntax_Syntax.U_zero] in
    let uu____4507 =
      let uu____4508 =
        let uu____4509 = FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit in
        let uu____4510 =
          let uu____4513 = FStar_Syntax_Syntax.as_arg a in [uu____4513] in
        uu____4509 :: uu____4510 in
      FStar_Syntax_Syntax.mk_Tm_app r uu____4508 in
    uu____4507 FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.pos
let synth:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun typ  ->
      fun tau  ->
        (let uu____4526 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "Tac") in
         FStar_ST.op_Colon_Equals tacdbg uu____4526);
        (let uu____4546 =
           let uu____4553 = reify_tactic tau in
           run_tactic_on_typ uu____4553 env typ in
         match uu____4546 with
         | (gs,w) ->
             let uu____4560 =
               FStar_List.existsML
                 (fun g  ->
                    let uu____4564 =
                      let uu____4565 =
                        getprop g.FStar_Tactics_Types.context
                          g.FStar_Tactics_Types.goal_ty in
                      FStar_Option.isSome uu____4565 in
                    Prims.op_Negation uu____4564) gs in
             if uu____4560
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_OpenGoalsInSynthesis,
                   "synthesis left open goals") typ.FStar_Syntax_Syntax.pos
             else w)